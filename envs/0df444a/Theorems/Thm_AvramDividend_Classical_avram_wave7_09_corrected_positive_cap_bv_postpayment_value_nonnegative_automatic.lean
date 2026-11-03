-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_corrected_positive_cap_bv_postpayment_value_nonnegative_automatic
-- name    : AvramDividend.Classical.avram_wave7_09_corrected_positive_cap_bv_postpayment_value_nonnegative_automatic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:23:41.708612+00:00
-- url     : https://prove2.me/theorems/151fa4ac-ea6c-4b44-adb6-96a53c9a0893
-- title:
--   Corrected positive-cap BV pre-ruin candidate nonnegativity follows automatically from other exact assumptions
-- statement:
--   For the exact original capped dividend source X, cap C>0, original IsAdmissibleLe strategy D from reserve x with ENNReal.ofReal x≤C, a candidate w continuous on nonnegative reserves, with w(0)≥0, C1 on the strict capped positive HJB interior and derivative≥1 there, the source pre-ruin candidate nonnegativity ∀ω,t>0<ruinTime, 0≤w(riskProcess X x D t ω) follows automatically. Proved b3117b07 gives x≥0; Proved 15c076b4 puts every original pre-ruin riskProcess in [0,C]; Proved 2ba5cc4f yields w(y)≥w(0)+y≥0 throughout that closed cap. No stochastic HJB generator inequality, infinite horizon theorem, unproved import or changed process is used. This formally certifies the `hw_nonneg` hypothesis of corrected parent 8c16239e is redundant given its other BV positive-cap gradient assumptions.
-- source:
--   Proved b3117b07, 15c076b4, 2ba5cc4f; exact original Ω/P/𝓕/X, riskProcess, ruinTime and IsAdmissibleLe.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_corrected_positive_cap_bv_postpayment_value_nonnegative_automatic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) := by sorry
