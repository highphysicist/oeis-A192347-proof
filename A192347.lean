import Mathlib

-- The already accepted coefficient recurrence.
def coeff : Nat → Int × Int
  | 0 => (1, 0)
  | 1 => (0, 1)
  | n + 2 =>
      let u := coeff (n + 1)
      let v := coeff n
      (2 * u.2 + v.1, 2 * (u.1 + u.2) + v.2)

private theorem coeff_step (n : Nat) :
    coeff (n + 2) =
      (2 * (coeff (n + 1)).2 + (coeff n).1,
       2 * ((coeff (n + 1)).1 + (coeff (n + 1)).2) + (coeff n).2) := by
  simp [coeff]

theorem coeff_recurrence (n : Nat) :
    (coeff (n + 4)).1 =
      2 * (coeff (n + 3)).1 + 6 * (coeff (n + 2)).1 -
      2 * (coeff (n + 1)).1 - (coeff n).1 := by
  rw [coeff_step (n + 2), coeff_step (n + 1), coeff_step n]
  simp only [Prod.fst, Prod.snd]
  ring

noncomputable def oeisPoly : Nat → Polynomial Int
  | 0 => 1
  | 1 => Polynomial.X
  | n + 2 =>
      2 * Polynomial.X * oeisPoly (n + 1) +
      (Polynomial.X + 2 - Polynomial.X ^ 2) * oeisPoly n

-- Quotient evaluation: x^2 = x+1 identifies reduced polynomial coordinates.
theorem oeisPoly_eval_bridge {R : Type*} [CommRing R]
    (x : R) (hx : x ^ 2 = x + 1) (n : Nat) :
    (oeisPoly n).eval₂ (Int.castRingHom R) x =
      ((coeff n).1 : R) + ((coeff n).2 : R) * x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [oeisPoly, coeff]
  | one => simp [oeisPoly, coeff]
  | more n ih0 ih1 =>
      rw [oeisPoly]
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
        Polynomial.eval₂_sub, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_ofNat]
      rw [ih1, ih0, coeff_step]
      simp only [Prod.fst, Prod.snd]
      push_cast
      linear_combination (2 * ((coeff (n + 1)).2 : R) - ((coeff n).1 : R) - ((coeff n).2 : R) * x) * hx

-- For any x,d with d^2=x+2, the radical formula equals twice the polynomial.
theorem oeisPoly_radical_bridge {R : Type*} [CommRing R]
    (x d : R) (hd : d ^ 2 = x + 2) (n : Nat) :
    2 * (oeisPoly n).eval₂ (Int.castRingHom R) x =
      (x + d) ^ n + (x - d) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [oeisPoly]; ring
  | one => simp [oeisPoly]; ring
  | more n ih0 ih1 =>
      have hplus : (x + d) ^ 2 = 2 * x * (x + d) + (x + 2 - x ^ 2) := by
        calc
          (x + d) ^ 2 = 2 * x * (x + d) + (d ^ 2 - x ^ 2) := by ring
          _ = _ := by rw [hd]
      have hminus : (x - d) ^ 2 = 2 * x * (x - d) + (x + 2 - x ^ 2) := by
        calc
          (x - d) ^ 2 = 2 * x * (x - d) + (d ^ 2 - x ^ 2) := by ring
          _ = _ := by rw [hd]
      have hstep :
          (x + d) ^ (n + 2) + (x - d) ^ (n + 2) =
          2 * x * ((x + d) ^ (n + 1) + (x - d) ^ (n + 1)) +
          (x + 2 - x ^ 2) * ((x + d) ^ n + (x - d) ^ n) := by
        have hp : (x + d) ^ (n + 2) = (x + d) ^ n * (x + d) ^ 2 := by
          rw [pow_add]
        have hm : (x - d) ^ (n + 2) = (x - d) ^ n * (x - d) ^ 2 := by
          rw [pow_add]
        have hp1 : (x + d) ^ (n + 1) = (x + d) ^ n * (x + d) := by
          rw [pow_succ]
        have hm1 : (x - d) ^ (n + 1) = (x - d) ^ n * (x - d) := by
          rw [pow_succ]
        rw [hp, hm, hp1, hm1, hplus, hminus]
        ring
      rw [oeisPoly]
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
        Polynomial.eval₂_sub, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_ofNat]
      calc
        2 * (2 * x * (oeisPoly (n + 1)).eval₂ (Int.castRingHom R) x +
          (x + 2 - x ^ 2) * (oeisPoly n).eval₂ (Int.castRingHom R) x) =
          2 * x * (2 * (oeisPoly (n + 1)).eval₂ (Int.castRingHom R) x) +
          (x + 2 - x ^ 2) * (2 * (oeisPoly n).eval₂ (Int.castRingHom R) x) := by ring
        _ = (x + d) ^ (n + 2) + (x - d) ^ (n + 2) := by
          rw [ih1, ih0]
          exact hstep.symm

theorem A192346_conjecture (n : Nat) :
    (coeff (n + 4)).1 =
      2 * (coeff (n + 3)).1 + 6 * (coeff (n + 2)).1 -
      2 * (coeff (n + 1)).1 - (coeff n).1 := coeff_recurrence n

-- The second coordinate is the coefficient of X in the reduced polynomial.
theorem coeff_second_recurrence (n : Nat) :
    (coeff (n + 4)).2 =
      2 * (coeff (n + 3)).2 + 6 * (coeff (n + 2)).2 -
      2 * (coeff (n + 1)).2 - (coeff n).2 := by
  rw [coeff_step (n + 2), coeff_step (n + 1), coeff_step n]
  simp only [Prod.fst, Prod.snd]
  ring

-- A192347 has offset 1: a(1) is the X coefficient of p_0.
def oeisA192347 (n : Nat) : Int := (coeff (n - 1)).2

theorem oeisA192347_initial :
    oeisA192347 1 = 0 ∧ oeisA192347 2 = 1 ∧
    oeisA192347 3 = 2 ∧ oeisA192347 4 = 11 := by
  decide

theorem oeisA192347_recurrence (n : Nat) (hn : 1 ≤ n) :
    oeisA192347 (n + 4) =
      2 * oeisA192347 (n + 3) + 6 * oeisA192347 (n + 2) -
      2 * oeisA192347 (n + 1) - oeisA192347 n := by
  cases n with
  | zero => omega
  | succ k =>
      simpa [oeisA192347, Nat.succ_eq_add_one, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using coeff_second_recurrence k

#print axioms coeff_second_recurrence
#print axioms oeisPoly_eval_bridge
#print axioms oeisPoly_radical_bridge
#print axioms oeisA192347_recurrence
