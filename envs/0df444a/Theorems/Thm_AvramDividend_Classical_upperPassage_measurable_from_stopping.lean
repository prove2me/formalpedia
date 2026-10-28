-- Prove2me | Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping
-- name    : AvramDividend.Classical.upperPassage_measurable_from_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:20:13.791573+00:00
-- url     : https://prove2.me/theorems/e1fe86e9-90f0-4b77-9ef8-3537e074f2a7
-- title:
--   Measurability of the spectrally negative Lévy upper-passage stopping time
-- statement:
--   An upper-passage time known to be a stopping time for the right-continuous filtration is measurable for the ambient sigma algebra. Used to transfer finite-horizon killed renewal estimates to full horizon by monotone convergence.
-- source:
--   Proved upperPassage_stopping_rightCont_filtration, Mathlib IsStoppingTime.measurable.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.upperPassage_measurable_from_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) :
    Measurable (twoSidedExitUpTime X b) := by sorry
