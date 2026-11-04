-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_orthogonal_finite_L2_square_identity
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_orthogonal_finite_L2_square_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:46:20.368041+00:00
-- url     : https://prove2.me/theorems/9c3483da-dd90-40b4-a1f3-d11ecfc535f0
-- title:
--   Finite actual-space pairwise-orthogonal compensated jump steps obey exact L2 square sum
-- statement:
--   For finitely many actual original-space increment random variables F_i, assume every pairwise product is integrable and each distinct pair has zero expectation of its product. Then the expected square of the finite sum is exactly the sum of the expected squares. This is the finite algebraic isometry component required after proving conditional orthogonality for genuine source predictable jump-count increments. The source orthogonality premises are explicit and are not claimed from first-moment rectangle compensation.
-- source:
--   Use Finset.sum_mul_sum, integrable_finset_sum, integral_finset_sum and Finset.sum_eq_single. All covariance assumptions remain explicit.

import Mathlib
open MeasureTheory

theorem AvramDividend.Classical.avram_p4_b_smalljump_orthogonal_finite_L2_square_identity
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : Finset ι) (F : ι → Ω → ℝ)
    (hProd : ∀ i ∈ S, ∀ j ∈ S,
      Integrable (fun ω => F i ω * F j ω) P)
    (hOrth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (∫ ω, F i ω * F j ω ∂P) = 0) :
    (∫ ω, (∑ i ∈ S, F i ω)^2 ∂P) =
      ∑ i ∈ S, ∫ ω, (F i ω)^2 ∂P := by sorry
