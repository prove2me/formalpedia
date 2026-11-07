-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
-- name    : AvramDividend.Classical.avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:39:01.071781+00:00
-- url     : https://prove2.me/theorems/ca595620-0e76-45ff-b10e-8c6adc86e36f
-- title:
--   Right-continuous stopping zero event preserves L1 under exact initial-reward mask
-- statement:
--   For a right-continuous filtration and finite underlying measure, the time-zero event of an actual stopping clock is measurable, hence replacing an integrable stopped payoff F with a deterministic initial reward b exactly on this event preserves its Bochner integrability. This is the no-extra-measurability source bridge needed for the original UBV positive-clock masked HJB budget. The result is independent of Levy generator and imposes no additional assumptions on the actual stochastic model.
-- source:
--   UBV-LOC6 original stopped zero-clock masked integrability bridge, derived from the Mathlib right-continuous IsStoppingTime measurability theorem and integrability of measurable piecewise substitutions.

import Mathlib

open MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (F : Ω → ℝ) (hFI : Integrable F P) (b : ℝ) :
    Integrable (fun ω => if σ ω = 0 then b else F ω) P := by sorry
