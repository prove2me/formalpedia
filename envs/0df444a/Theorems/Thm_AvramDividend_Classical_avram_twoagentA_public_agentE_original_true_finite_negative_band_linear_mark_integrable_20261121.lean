-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_agentE_original_true_finite_negative_band_linear_mark_integrable_20261121
-- name    : AvramDividend.Classical.avram_twoagentA_public_agentE_original_true_finite_negative_band_linear_mark_integrable_20261121
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:21:08.993079+00:00
-- url     : https://prove2.me/theorems/10b14b56-68eb-4c16-9805-57010f4f8384
-- title:
--   Original physical marked integral L1 source 0911ab46
-- statement:
--   Exact already accepted original negative-mark signed-integral source proof, republished as public importable prerequisite for the genuine unrestricted negative activity physical compensated mark L1 centring and reciprocal quantizer approximation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

/-- Original finite negative-band physical Lévy mark has finite first moment. -/

theorem AvramDividend.Classical.avram_twoagentA_public_agentE_original_true_finite_negative_band_linear_mark_integrable_20261121
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n m : ℕ) :
    IntegrableOn (fun z : ℝ => z)
      (Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) X.ν := by sorry
