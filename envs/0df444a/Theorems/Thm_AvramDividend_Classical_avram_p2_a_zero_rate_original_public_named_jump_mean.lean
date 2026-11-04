-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_public_named_jump_mean
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_public_named_jump_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:31:40.091991+00:00
-- url     : https://prove2.me/theorems/6b0dd0e4-d4ae-43a0-bcc4-7b48f536cf5c
-- title:
--   Original integrable finite marked jump-test mean from public pathwise and uniform integrability interfaces
-- statement:
--   For the actual original Lévy process, a continuous signed test with an explicit separated-negative finite envelope has an integrable finite significant-jump sum and its expected uniform-grid sums converge to the expectation of that very same pathwise sum. All jumps are on the original sample space; no rate or compensator is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_exact_significant_jump_grid_limit
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_real_nnreal_uniform_step_coe
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_signed_uniform_mesh_measurable_expectations

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_public_named_jump_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hXm : ∀ t : ℝ≥0, Measurable (X.X t))
    (g : ℝ → ℝ) (hg : Continuous g)
    (T : ℝ≥0) (hT : 0 < T)
    (ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (hvanish : ∀ y : ℝ, |y| < ρ → g y = 0)
    (M : ENNReal) (hM : M ≠ ⊤)
    (hbound : ∀ y : ℝ, ‖g y‖ₑ ≤ if y ≤ -ε then M else 0) :
    ∃ J : Ω → ℝ, Integrable J P ∧
      (∀ ω : Ω, ∃ F : Finset ℝ≥0,
        (∀ t : ℝ≥0, t ∈ F ↔ 0 < t ∧ t ≤ T ∧
          ρ ≤ |X.X t ω -
            Function.leftLim (fun u : ℝ≥0 => X.X u ω) t|) ∧
        J ω = ∑ t ∈ F,
          g (X.X t ω -
            Function.leftLim (fun u : ℝ≥0 => X.X u ω) t)) ∧
      Tendsto (fun n : ℕ => ∫ ω,
        (∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) *
                Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω -
             X.X ((i : ℝ≥0) *
                Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω)) ∂P)
        atTop (𝓝 (∫ ω, J ω ∂P)) := by sorry
