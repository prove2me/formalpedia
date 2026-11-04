-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_real_unit_high_moment_le_mass
-- name    : AvramDividend.Classical.avram_p2_i_moment_real_unit_high_moment_le_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:44:42.647631+00:00
-- url     : https://prove2.me/theorems/5b2acf62-defc-4276-a3c7-6cdc258b81ba
-- title:
--   Real-valued high moments of a unit-supported finite measure are bounded by its total mass
-- statement:
--   Let a positive Borel measure on the real line be concentrated in [0,1]. If the constant one and kth monomial are real-integrable, then its real kth moment does not exceed the real integral of one, that is, its finite total mass. This companion of the ENNReal moment bound supplies the comparison required to apply convergence of ordinary real moment integrals.

import Mathlib
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.avram_p2_i_moment_real_unit_high_moment_le_mass
    (μ : Measure ℝ) (hμ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hOne : Integrable (fun _ : ℝ => (1 : ℝ)) μ)
    (k : ℕ) (hk : Integrable (fun z : ℝ => z ^ k) μ) :
    (∫ z : ℝ, z ^ k ∂μ) ≤ (∫ _ : ℝ, (1 : ℝ) ∂μ) := by sorry
