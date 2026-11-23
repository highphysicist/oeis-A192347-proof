# OEIS A192347: proof of Colin Barker's recurrence conjecture

This repository formalizes the fourth-order recurrence conjectured by Colin Barker in 2013 for [OEIS A192347](https://oeis.org/A192347), the coefficient of `X` in the reduction of the polynomial family also used in [A192346](https://oeis.org/A192346).

## Theorem

Let `p_n(X) = ((X + sqrt(X+2))^n + (X - sqrt(X+2))^n)/2`, with `p_0=1` and `p_1=X`. Reduce modulo `X^2-X-1` and write the unique degree-at-most-one representative as `u_n+v_n X`. OEIS A192347 is `a(n+1)=v_n`.

For every `n >= 1`,

`a(n+4) = 2 a(n+3) + 6 a(n+2) - 2 a(n+1) - a(n)`.

Initial values: `a(1)=0`, `a(2)=1`, `a(3)=2`, `a(4)=11`.

## Proof

The polynomial family satisfies

`p_(n+2) = 2 X p_(n+1) + (X+2-X^2) p_n`.

In `Z[X]/(X^2-X-1)`, this becomes `p_(n+2)=2 X p_(n+1)+p_n`. Multiplication by `X` sends `(u,v)` to `(v,u+v)`, so the coefficient vectors obey

`w_(n+2)=2 M w_(n+1)+w_n`, with `M=[[0,1],[1,1]]`.

The characteristic polynomial `det(t^2 I-2tM-I)=t^4-2t^3-6t^2+2t+1` annihilates **both** coordinates. The second coordinate is A192347.

## Lean verification

`A192347.lean` reuses the accepted A192346 polynomial/radical bridges and adds `coeff_second_recurrence` and `oeisA192347_recurrence`. Run inside an installed Mathlib project:

```bash
lake env lean A192347.lean
```

Check the final `#print axioms` output: it must not contain `sorryAx`. **The complete `A192347.lean` source was reported to compile successfully in Colab on November 23, 2026.** Its axiom reports contained no `sorryAx`; only standard Lean axioms were reported.

The evaluation bridge characterizes the reduced polynomial in the quotient relation `X^2=X+1`; it does not invoke `Polynomial.modByMonic` directly.

## Attribution

Sequence by Clark Kimberling. Recurrence conjectured by Colin Barker (January 17, 2013). Formal proof development prepared November 23, 2026 for Shreyas Samir Kolte. Related A192346 proof: https://github.com/highphysicist/oeis-A192346-proof .

OEIS editorial status should be checked against the live entry; GitHub publication and editorial approval are distinct.
