-- Prove2me | Theorems.Thm_DerandLDT_observation_3_14
-- name    : DerandLDT.observation_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:05:03.566604+00:00
-- url     : https://prove2.me/theorems/b735ead0-c055-4681-b734-7c68b2be45bc
-- title:
--   Observation 3.14 — the resultant commutes with degree-preserving specialization
-- statement:
--   Let $f(X, Y, Z), g(X, Y, Z) \in \mathbb F[X, Y, Z]$ have $Z$-degree at least one, and let $a \in \mathbb F^2$ be such that $\deg_Z f(X, Y, Z) = \deg_Z f(a, Z)$ and $\deg_Z g(X, Y, Z) = \deg_Z g(a, Z)$. Then
--   $$
--   \mathrm{Res}_Z\big(f(X, Y, Z), g(X, Y, Z)\big)(a) = \mathrm{Res}_Z\big(f(a, Z), g(a, Z)\big).
--   $$
--   It lets the proof of Theorem 1.2 transfer the nonvanishing of $\mathrm{Disc}_Z$ at a point to the univariate polynomials $\hat Q(a, Z)$.
--
--   **Formalization Note** $\mathbb F[X, Y, Z]$ is represented as $\mathbb F[X, Y][Z]$ (`Polynomial (MvPolynomial (Fin 2) F)`), $f(a, Z)$ is the coefficientwise evaluation at $a$, and $\mathrm{Res}_Z$ is Mathlib's resultant with the $Z$-degrees as sizes.
--
--   Differences from the source:
--   - encoding: f, g ∈ F[X, Y, Z] viewed as univariates in Z → f, g ∈ F[X, Y][Z]; reason: canonical isomorphism
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Observation 3.14, p.13

import Mathlib

set_option autoImplicit false

universe u

namespace DerandLDT

open Polynomial

/-- **Observation 3.14** (the resultant commutes with degree-preserving specialization).
Harsha, Kopparty, Kumar, Saptharishi, Sudan, *On derandomizing the line-point
low-degree test*, STOC 2027 submission manuscript (sha256 d57e7d6f…80df), Observation 3.14, p.13: *Let `f(X, Y, Z), g(X, Y, Z) ∈ F[X, Y, Z]` have `Z`-degree at
least one and let `a ∈ F²` be such that `deg_Z f(X, Y, Z) = deg_Z f(a, Z)` and
`deg_Z g(X, Y, Z) = deg_Z g(a, Z)`. Then `Res_Z(f, g) ∈ F[X, Y]` evaluated at `a` equals
`Res_Z(f(a, Z), g(a, Z))`.*

**Formalization Note.** `F[X, Y, Z]` is `F[X, Y][Z]`: polynomials in `Z` (`Polynomial`) with
coefficients in `MvPolynomial (Fin 2) F` (variables `X = 0`, `Y = 1`). `f(a, Z)` is
`f.map (eval a)`, and `Res_Z` is Mathlib's `Polynomial.resultant` with the default sizes
(the `Z`-degrees). -/
theorem observation_3_14 (F : Type u) [Field F] (f g : Polynomial (MvPolynomial (Fin 2) F))
    (hf : 1 ≤ f.natDegree) (hg : 1 ≤ g.natDegree) (a : Fin 2 → F)
    (hfa : (f.map (MvPolynomial.eval a)).natDegree = f.natDegree)
    (hga : (g.map (MvPolynomial.eval a)).natDegree = g.natDegree) :
    MvPolynomial.eval a (resultant f g) =
      resultant (f.map (MvPolynomial.eval a)) (g.map (MvPolynomial.eval a)) := by sorry

end DerandLDT
