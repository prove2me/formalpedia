-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_all_sources_zero_cap_all_strategy_full_value_iff_barrier_value
-- name    : AvramDividend.Classical.avram_wave7_09_all_sources_zero_cap_all_strategy_full_value_iff_barrier_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:52:47.79619+00:00
-- url     : https://prove2.me/theorems/47cd00d9-0824-4887-b968-5b372f237404
-- title:
--   All original sources: cap-zero all-strategy full-value budget iff actual zero-barrier value fits
-- statement:
--   For every genuine Standing spectrally negative Lévy process X, positive q and arbitrary ENNReal allowance A, every admissible cap-zero strategy from reserve zero has full dividendValue≤A if and only if the actual zero-barrier strategy has full dividendValue≤A. This sharp exact zero-cap all-strategy criterion requires no bounded/unbounded variation split, finite negative-jump activity or closed-form reflected value. The proof uses only Proved source-process cap-zero domination 570b5248 and genuine zero-barrier admissibility 32b4ccb8, preserving Ω,P,filtration,X,dividendMeasure and dividendValue. For finite-activity BV sources, the accepted W7-09 first-jump formula then computes the threshold.
-- source:
--   Original source X,P,filtration, ruinTime, dividendMeasure and dividendValue; no Open imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_all_sources_zero_cap_all_strategy_full_value_iff_barrier_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (A : ℝ≥0∞) :
    (∀ (D : ℝ≥0 → Ω → ℝ),
      IsAdmissibleLe X 0 (0 : ℝ≥0∞) D →
      dividendValue X q 0 D ≤ A) ↔
    dividendValue X q 0 (barrierStrategy X 0 0) ≤ A  := by sorry
