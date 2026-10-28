-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_adapted
-- name    : AvramDividend.Classical.reflectedSup_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:23:36.725154+00:00
-- url     : https://prove2.me/theorems/63c373fc-af88-4611-997b-4773628cc31a
-- title:
--   The actual reflected spectrally negative Lévy process is adapted to its natural filtration
-- statement:
--   The actual reflected drawdown R_t=sup_{s≤t} X_s−X_t is adapted to the given filtration of any spectrally negative Lévy process. Running supremum is adapted because it agrees with the zero-barrier strategy at zero initial capital, whose adaptedness is already proved. The difference between this adapted process and the adapted Lévy path is adapted by the subtraction theorem. This is a necessary measurable-process interface for constructing first-passage times of excursion heights.
-- source:
--   Existing Prove2Me barrierStrategy_adapted and barrierStrategy_self_eq_runningSup, and pinned Mathlib MeasureTheory.Adapted.sub.

import Mathlib.Probability.Process.Adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_adapted
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Definitions.Def_AvramDividend_Classical_Reflection

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.reflectedSup_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Adapted 𝓕 (fun t : ℝ≥0 => fun ω : Ω => reflectedSup X t ω) := by sorry
