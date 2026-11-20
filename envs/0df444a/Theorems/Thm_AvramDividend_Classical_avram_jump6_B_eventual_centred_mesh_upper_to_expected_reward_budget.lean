-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_eventual_centred_mesh_upper_to_expected_reward_budget
-- name    : AvramDividend.Classical.avram_jump6_B_eventual_centred_mesh_upper_to_expected_reward_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:04:53.106989+00:00
-- url     : https://prove2.me/theorems/eca6904d-1b93-4415-8559-867b08877b3c
-- title:
--   Eventual centred finite-grid reward domination yields exact expected budget
-- statement:
--   If an integrable stopped reward is eventually below b plus a mean-zero integrable grid martingale plus any positive epsilon, its expected value is at most b. Integrate one fine-grid inequality and send epsilon to zero. This applies to original Levy stopped physical-grid budgets.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_eventual_centred_mesh_upper_to_expected_reward_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → ℝ) (M : ℕ → Ω → ℝ) (b : ℝ)
    (hFI : Integrable F P)
    (hMI : ∀ j, Integrable (M j) P)
    (hMzero : ∀ j, (∫ ω, M j ω ∂P) = 0)
    (hUpper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop,
        ∀ᵐ ω ∂P, F ω ≤ b + M j ω + ε) :
    (∫ ω, F ω ∂P) ≤ b := by sorry
