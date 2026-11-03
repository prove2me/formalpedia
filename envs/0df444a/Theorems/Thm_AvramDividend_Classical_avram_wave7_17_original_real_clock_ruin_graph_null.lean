-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_real_clock_ruin_graph_null
-- name    : AvramDividend.Classical.avram_wave7_17_original_real_clock_ruin_graph_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:46:31.09352+00:00
-- url     : https://prove2.me/theorems/0d3c8f05-e1d1-41dc-829b-f8b29336676a
-- title:
--   Actual original Lévy ruin-time graph has zero P × physical real Lebesgue mass
-- statement:
--   Under the original source Lévy process, filtration and dividend strategy, the time-space graph where positive real clock time equals the source ruin time has zero original P × physical real Lebesgue measure. The stopping time is measurable. Each sample's nonnegative real-time fibre is at most one point. This justifies exchanging inclusive predictable stopping and strict physical-clock integration almost everywhere, while leaving the actual Stieltjes atoms and jump at ruin intact. This is a genuine original-process lemma rather than an expected cash bound.
-- source:
--   Source ruinTime and Proved ruinTime_measurable of the original SpectrallyNegativeLevy. Mathlib Measure.measure_prod_null_of_ae_null, null singletons under real Lebesgue volume.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_real_clock_ruin_graph_null
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    (P.prod (volume : Measure ℝ))
      {p : Ω × ℝ |
        0 ≤ p.2 ∧ ENNReal.ofReal p.2 = ruinTime X x D p.1} = 0 := by sorry
