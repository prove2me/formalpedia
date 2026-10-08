-- Prove2me | Theorems.Thm_ConnesRZNative_bounded_column_synthesis_with_adjoint_energy
-- name    : ConnesRZNative.bounded_column_synthesis_with_adjoint_energy
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-06T23:21:52.325113+00:00
-- url     : https://prove2.me/theorems/158e0d61-3e13-4260-ae16-9c09458cfeb9
-- title:
--   Bounded synthesis of square-summable Hilbert columns with exact adjoint energy and uniqueness
-- statement:
--   Let $H$ be a complete complex Hilbert space and $(v_i)_{i\in I}$ a family with $\sum_i\|v_i\|^2<\infty$. There is a unique bounded complex-linear map $S:\ell^2(I,\mathbb C)\to H$ having these basis columns. It is given by the absolutely convergent synthesis series $Su=\sum_i u_i v_i$, satisfies $\|S\|^2\le\sum_i\|v_i\|^2$, and its adjoint obeys
--   $$ (S^*h)_i=\langle v_i,h\rangle,\qquad \|S^*h\|^2=\sum_i|\langle v_i,h\rangle|^2.$$
--   The Hilbert inner product is conjugate-linear in its first argument. All sums are unconditional, and no countability assumption on $I$ is required.
--
--   This is the functional-analytic construction used in the Connes–Weil Green-column frontier: it derives bounded synthesis, exact adjoint norms, and uniqueness from square-summable supplied columns. Its hypothesis is square summability of those columns; it does not construct a physical Green metric, prove a zeta-zero counting bound, or prove RH. Identification with an existing native operator requires the same coefficient carrier and the same basis columns.
-- source:
--   Repository monocap-tech/weil, WeilDefect/Connes/ColumnSynthesis.lean: columnSynthesis_apply, columnSynthesis_single, columnSynthesis_adjoint_coordinate, columnSynthesis_adjoint_norm_sq, columnSynthesis_norm_sq_le, columnSynthesis_unique. Cauchy–Schwarz synthesis construction and Parseval identity; supporting generic analytic result for the actual-zero Green frontier.

import Mathlib
open scoped BigOperators InnerProductSpace lp ENNReal Classical

theorem ConnesRZNative.bounded_column_synthesis_with_adjoint_energy {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (v : ι → H) (hv : Summable (fun i => ‖v i‖ ^ 2)) :
    ∃ S : ℓ²(ι, ℂ) →L[ℂ] H,
      (∀ u, S u = ∑' i, u i • v i) ∧
      (∀ i, S (lp.single 2 i (1 : ℂ)) = v i) ∧
      (∀ h i, (ContinuousLinearMap.adjoint S) h i = ⟪v i, h⟫_ℂ) ∧
      (∀ h, ‖(ContinuousLinearMap.adjoint S) h‖ ^ 2 = ∑' i, ‖⟪v i, h⟫_ℂ‖ ^ 2) ∧
      ‖S‖ ^ 2 ≤ ∑' i, ‖v i‖ ^ 2 ∧
      (∀ T : ℓ²(ι, ℂ) →L[ℂ] H,
        (∀ i, T (lp.single 2 i (1 : ℂ)) = v i) → T = S) := by sorry
