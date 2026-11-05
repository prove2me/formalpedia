-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_integration_original_unit_expected_mark_cutoff_finite
-- name    : AvramDividend.Classical.avram_integration_original_unit_expected_mark_cutoff_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:24:28.492942+00:00
-- url     : https://prove2.me/theorems/1aad71c3-6d7a-4017-89ed-e90ef23ea42f
-- title:
--   Genuine original unit-time intrinsic negative-mark expectation measure finite on separated cutoff
-- statement:
--   For the original Levy process, jointly extract its genuine unit-time expected intrinsic jump-mark measure and prove that this same measure is finite on any strictly negative cutoff Iic(-eps). This supplies the finite-measure side of the compact-test uniqueness step toward original Borel rates.
-- source:
--   Source-exact integration of independently Proved original intrinsic mark expectation measure 9bbf7f85-18e1-4606-9d47-36dd5920b91d and original negative halfline expected count finiteness 6b9a98be-89bb-4eec-b9f0-fdfd98b091ba. Consumer 6169a734-f844-4e24-b278-0713a6f113b9; its full threshold equality remains Open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_integration_original_unit_expected_mark_cutoff_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : Measure ℝ,
      (∀ B : Set ℝ, MeasurableSet B →
        μ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P)) ∧
      μ (Iic (-ε)) ≠ ⊤ := by sorry
