-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_forall_lt_taylorCoeff_eq_zero_iff_le_ord
-- name    : AlgebraicCurve.Place.forall_lt_taylorCoeff_eq_zero_iff_le_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/4180b69d-5502-509a-81bd-2557abe21c75
-- title:
--   Vanishing of the first e Taylor coefficients means ordᵥ f ≥ e
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$, i.e. a valuation subring $\mathcal{O}_v =$ `v.toValuationSubring` of $F$ containing the image of $K$, different from $F$ itself, and a principal ideal ring. Assume $v$ is rational, in the sense that the structure map from $K$ to the residue field of $\mathcal{O}_v$ is surjective. Let $t \in F$ satisfy $\mathrm{ord}_v t = 1$, where $\mathrm{ord}_v$ is minus the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation of the height-one spectrum point attached to $v$; let $f \in \mathcal{O}_v$ be nonzero, and let $e$ be a natural number. Then the first $e$ Taylor coefficients of $f$ at $v$ along $t$ vanish — that is, `taylorCoeff v t q f = 0` for all $q < e$, where `taylorCoeff v t q f` is the regularised value `evalAt` of the $q$-th remainder of the recursion $R_0 = f$, $R_{r+1} = (R_r - \mathrm{ev}_v(R_r))t^{-1}$, and `evalAt g` is the preimage in $K$ under the residue map of the residue class of $g$ when $g \in \mathcal{O}_v$ and $0$ otherwise — if and only if $e \le \mathrm{ord}_v f$ as integers.
--
--   This identifies the order of vanishing of a regular function at a rational place with the index of the first nonvanishing Taylor coefficient along a uniformiser, so that the vanishing condition on the initial coefficients is independent of the choice of uniformiser. It is used for the nonvanishing of the $\mathrm{ord}_v f$-th Taylor coefficient, for the invertibility criterion for jet matrices in terms of Riemann–Roch spaces, and in the Jensen-type estimates on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_forall_lt_taylorCoeff_eq_zero_iff_le_ord.lean

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.forall_lt_taylorCoeff_eq_zero_iff_le_ord
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f : F}
    (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) (e : ℕ) :
    (∀ q, q < e → taylorCoeff v t q f = 0) ↔ (e : ℤ) ≤ v.ord f := by sorry
