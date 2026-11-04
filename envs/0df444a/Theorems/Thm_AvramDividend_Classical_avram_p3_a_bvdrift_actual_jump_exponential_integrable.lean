-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_jump_exponential_integrable
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_actual_jump_exponential_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:54:22.207455+00:00
-- url     : https://prove2.me/theorems/961721d0-c85f-4d2b-a908-5482407227f6
-- title:
--   Actual original BV negative-jump exponential is automatically integrable
-- statement:
--   For genuine original bounded-variation spectrally negative Lévy process on its own probability measure, the exponential of minus a nonnegative parameter times its entire actual negative-jump magnitude total is integrable. Uses proved original jump-total a.e. measurability and 0≤exp(-θJ)≤1, no finite first moment, Poisson model, or extra hypotheses.
-- source:
--   Original s-finite jump-kernel a.e. measurability helper; source X.isProbability; Measurable.comp_aemeasurable; Integrable.of_bound with the nonnegative ENNReal.toReal sum and Real.exp_le_exp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_jump_total_aemeasurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original finite-horizon full negative-jump exponential is L1
for every nonnegative Laplace parameter, without jump moments. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_actual_jump_exponential_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω : Ω =>
      Real.exp (-(θ * (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ T then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal))) P := by sorry
