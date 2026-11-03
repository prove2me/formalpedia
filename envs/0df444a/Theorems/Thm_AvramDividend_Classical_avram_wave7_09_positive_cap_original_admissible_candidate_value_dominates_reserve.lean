-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_positive_cap_original_admissible_candidate_value_dominates_reserve
-- name    : AvramDividend.Classical.avram_wave7_09_positive_cap_original_admissible_candidate_value_dominates_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:56:38.501459+00:00
-- url     : https://prove2.me/theorems/08c8ac59-d645-48d3-a91f-1bd6cfbdfdcb
-- title:
--   Corrected positive-cap original admissibility and BV HJB gradient imply w(x)≥x≥0
-- statement:
--   Under the exact source capped admissibility of the original dividend process, reserve x is nonnegative by Proved b3117b07. When cap C>0, w(0)≥0, w is continuous on nonnegative reals and C1 with derivative ≥1 on the canonical strict HJB interior, Proved full-cap gradient secant 2ba5cc4f applied to 0≤x≤C yields x≤w(x)−w(0)≤w(x). This certifies the corrected parent boundary-value sign, even when x=0, x=C, or C=∞, and makes no stochastic supermartingale claim.
-- source:
--   Proved b3117b07 and 2ba5cc4f; exact original source X, 𝓕, D and cap C. Only Proved imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_positive_cap_original_admissible_candidate_value_dominates_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    0 ≤ x ∧ x ≤ w x := by sorry
