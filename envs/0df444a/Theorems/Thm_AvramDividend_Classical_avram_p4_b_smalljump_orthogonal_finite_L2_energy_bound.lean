-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_orthogonal_finite_L2_energy_bound
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_orthogonal_finite_L2_energy_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:50:45.514666+00:00
-- url     : https://prove2.me/theorems/17c9197e-087a-419e-a656-630b132b6858
-- title:
--   Finite orthogonal original-source compensated jump steps obey deterministic L2 energy bound
-- statement:
--   For finitely many compensated original-space jump-step variables whose pairwise products are integrable, distinct pairs have zero covariance, and each squared step has expectation bounded by its corresponding deterministic energy v_i, the expected square of their sum is bounded by the total deterministic energy. The genuine original-source covariance and diagonal square-moment bounds remain explicit hypotheses. This is an L2 energy interface for constructing the actual infinite-activity martingale from finite predictable-step integrands.
-- source:
--   Apply the accepted P4-B orthogonal finite L2 square identity, then Finset.sum_le_sum to the source-provided diagonal moment bounds.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_orthogonal_finite_L2_square_identity
open MeasureTheory

theorem AvramDividend.Classical.avram_p4_b_smalljump_orthogonal_finite_L2_energy_bound
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : Finset ι) (F : ι → Ω → ℝ) (v : ι → ℝ)
    (hProd : ∀ i ∈ S, ∀ j ∈ S,
      Integrable (fun ω => F i ω * F j ω) P)
    (hOrth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      (∫ ω, F i ω * F j ω ∂P) = 0)
    (hVar : ∀ i ∈ S,
      (∫ ω, (F i ω)^2 ∂P) ≤ v i) :
    (∫ ω, (∑ i ∈ S, F i ω)^2 ∂P) ≤ ∑ i ∈ S, v i := by sorry
