-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_nested_finite_L2_truncation_error
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_nested_finite_L2_truncation_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:11:38.108581+00:00
-- url     : https://prove2.me/theorems/41c795a8-4341-4571-8ea0-8af1ab5d4a30
-- title:
--   L2 squared difference of nested compensated finite jump-band sums bounded by omitted-band quadratic energy
-- statement:
--   Given actual source finite truncations S⊆T, pairwise orthogonality and finite second moments of band increments on the same probability space, the L2 squared error between the two truncation sums is bounded by the sum of variance budgets for the omitted bands T\S. No stochastic compensator assumptions are silently discharged.
-- source:
--   Finset.sum_sdiff, accepted P4-B finite L2 energy inequality, finite pairwise orthogonality.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_orthogonal_finite_L2_energy_bound
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_nested_finite_L2_truncation_error
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι] {P : Measure Ω}
    (S T : Finset ι) (hST : S ⊆ T)
    (F : ι → Ω → ℝ) (v : ι → ℝ)
    (hProd : ∀ i ∈ T, ∀ j ∈ T,
      Integrable (fun ω => F i ω * F j ω) P)
    (hOrth : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      (∫ ω, F i ω * F j ω ∂P) = 0)
    (hVar : ∀ i ∈ T,
      (∫ ω, (F i ω)^2 ∂P) ≤ v i) :
    (∫ ω, ((∑ i ∈ T, F i ω) - (∑ i ∈ S, F i ω))^2 ∂P) ≤ (∑ i ∈ T \ S, v i) := by sorry
