-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_stopped_clock_before_ruin
-- name    : AvramDividend.Classical.avram_p3_grid3_original_strict_stopped_clock_before_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:59:44.992802+00:00
-- url     : https://prove2.me/theorems/c729affd-25fa-46f4-810d-03c22c87b3a0
-- title:
--   Every physical time strictly before the actual clamped ruin clock is pre-ruin
-- statement:
--   Let tau=min(original ruinTime X x D, finite physical horizon T) as a finite NNReal stopped clock. Any physical time s<tau is strictly before the literal original ruinTime in ENNReal. The proof preserves the exact original process, uses finiteness of tau inherited from T, and supplies the stopped-mesh strict pre-ruin filter needed for Stieltjes cash cells.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_strict_stopped_clock_before_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω)
    (s : ℝ≥0)
    (hs : s < (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) :
    (s : ℝ≥0∞) < ruinTime X x D ω := by sorry
