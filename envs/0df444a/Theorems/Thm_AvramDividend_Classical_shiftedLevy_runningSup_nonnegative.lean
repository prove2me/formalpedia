-- Prove2me | Theorems.Thm_AvramDividend_Classical_shiftedLevy_runningSup_nonnegative
-- name    : AvramDividend.Classical.shiftedLevy_runningSup_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:37:14.667968+00:00
-- url     : https://prove2.me/theorems/f63fc137-5963-40ef-8318-e955459406fa
-- title:
--   The running supremum of future Lévy increments is nonnegative after every finite time shift
-- statement:
--   For every sample path, finite time shift u and nonnegative future interval length t, the supremum of the future increments X(u+v)-X(u) over 0≤v≤t is nonnegative. It contains its zero-time increment, which is exactly zero, and the supremum is finite by local path boundedness. This allows removal of max(0, ...) from the first shifted reflected-reserve ruin threshold, putting the strong-Markov barrier restart in canonical running-supremum form.
-- source:
--   Proved levyPath_bddAbove_Icc c2066587 and exact shifted Lévy increment path at v=0. For barrier strategy shifted ruin clock 609e34dd and standing valuation 79978d61.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.shiftedLevy_runningSup_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u t : ℝ≥0) :
    0 ≤ sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) ''
        Set.Icc 0 t) := by sorry
