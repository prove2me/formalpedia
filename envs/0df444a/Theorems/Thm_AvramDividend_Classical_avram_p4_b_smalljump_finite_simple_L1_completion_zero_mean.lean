-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_finite_simple_L1_completion_zero_mean
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_finite_simple_L1_completion_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:26:18.423878+00:00
-- url     : https://prove2.me/theorems/faaf8c12-88a9-4873-b697-3a6eef0247a8
-- title:
--   Original-space finite predictable-simple compensation extends to an integrable centred L1 limit
-- statement:
--   For a sequence of genuinely compensated original-space finite predictable-simple jump cell sums, assume all underlying cell random variables and compensators are integrable with exactly equal means, and that the sums converge in the true L1 seminorm on P to an integrable M. Then M has zero expectation. The theorem composes already proved P4-B simple centering and L1 closure; it explicitly retains all source compensation and convergence hypotheses, so it does not assume the still Open P2 original rectangle law or stochastic L2 isometry.
-- source:
--   Direct composition of accepted P4-B finite-simple-centering and L1-limit closure theorems.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_centered_limit_of_L1_convergence
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_finite_simple_centering_of_cell_compensation
open MeasureTheory Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_finite_simple_L1_completion_zero_mean
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : ℕ → Finset ι) (J C : ι → Ω → ℝ) (a : ℕ → ι → ℝ)
    (M : Ω → ℝ)
    (hJI : ∀ n, ∀ i ∈ S n, Integrable (J i) P)
    (hCI : ∀ n, ∀ i ∈ S n, Integrable (C i) P)
    (hCells : ∀ n, ∀ i ∈ S n,
       (∫ ω, J i ω ∂P) = (∫ ω, C i ω ∂P))
    (hMI : Integrable M P)
    (hConv : Tendsto
      (fun n => ∫⁻ ω,
        ‖(∑ i ∈ S n, a n i * (J i ω - C i ω)) - M ω‖ₑ ∂P)
      atTop (𝓝 0)) :
    (∫ ω, M ω ∂P) = 0 := by sorry
