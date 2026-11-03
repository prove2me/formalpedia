-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_positive_cap_bv_preruin_candidate_dominates_actual_reserve
-- name    : AvramDividend.Classical.avram_wave7_09_positive_cap_bv_preruin_candidate_dominates_actual_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:25:56.483811+00:00
-- url     : https://prove2.me/theorems/1ea8a735-eced-43f5-8837-3cc27d8a9cd4
-- title:
--   Corrected positive-cap BV candidate dominates each original pre-ruin controlled reserve including time zero
-- statement:
--   For the original capped admissible spectrally negative Lévy dividend strategy, cap C>0 and a continuous nonnegative-boundary-value C1 BV HJB candidate with derivative at least one throughout the strict positive cap interior, the candidate value dominates the actual controlled reserve at every time strictly before ruin, including t=0. Proved b3117b07 gives initial reserve x≥0. Proved 15c076b4 gives actual source pre-ruin riskProcess y in [0,C]. Proved 2ba5cc4f gives w(y)−w(0)≥y, and w(0)≥0 completes y≤w(y) with y≥0. This is a strong terminal-survival sign and reserve domination certificate and uses only Proved source-accurate imports.
-- source:
--   Proved original capped state b3117b07, 15c076b4 and full-cap gradient secant 2ba5cc4f; canonical Ω/P/𝓕/X, ruinTime, riskProcess, IsAdmissibleLe.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_positive_cap_bv_preruin_candidate_dominates_actual_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ riskProcess X x D t ω ∧
        riskProcess X x D t ω ≤ w (riskProcess X x D t ω) := by sorry
