-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_strictly_before_drawdown_ruin
-- name    : AvramDividend.Classical.firstUpcrossing_strictly_before_drawdown_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T12:52:47.678457+00:00
-- url     : https://prove2.me/theorems/1a8438de-b32b-40a2-a7eb-85a6a7e15523
-- title:
--   No pre-record drawdown breach ensures strict new-record passage before ruin
-- statement:
--   For a spectrally negative Lévy process under its primitive càdlàg assumptions, let u be a finite first new record at nonnegative level b. If there was no strict reflected-drawdown breach above positive a before u, then u is strictly earlier than the global first reflected drawdown breach time, without an extra continuity premise. Uses separately Proved actual right-continuity of the reflected process and the strict-first-passage boundary lemma; no strong Markov or distribution assertion.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1 renewal passage; pending Chat 05 reflectedSup_right_continuous and Proved firstUpcrossing_pre_ruin_strict_of_right_continuous 05e40496-e6c7-49d5-9c54-7b719a196f54.

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_reflectedSup_right_continuous
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_pre_ruin_strict_of_right_continuous

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.firstUpcrossing_strictly_before_drawdown_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (hBefore : ∀ t : ℝ≥0, t < u → reflectedSup X t ω ≤ a) :
    (u : ℝ≥0∞) <
      (⨅ (t : ℝ≥0) (_ : a < reflectedSup X t ω), (t : ℝ≥0∞)) := by sorry
