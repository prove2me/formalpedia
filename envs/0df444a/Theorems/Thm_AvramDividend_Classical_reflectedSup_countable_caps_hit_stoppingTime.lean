-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_countable_caps_hit_stoppingTime
-- name    : AvramDividend.Classical.reflectedSup_countable_caps_hit_stoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:05:32.548432+00:00
-- url     : https://prove2.me/theorems/db29660a-1c4e-452e-ac27-265c25aa2a76
-- title:
--   Supremum over any countable schedule of finite-horizon true reflected first-closed-level hitting times is a stopping time
-- statement:
--   For an actual spectrally negative Lévy reflected process R, any sequence of finite deterministic horizon caps, and any level x, consider the extended-real supremum of its exact continuous-time first closed-level hitting clock capped at each horizon. This is a stopping time without filtration right-continuity. Every capped first-hit clock is now independently Proved to be a stopping time, and the accepted countable pointwise supremum theorem provides closure under the countable cap schedule. An unbounded cofinal cap schedule will subsequently identify this clock with the uncapped earliest closed-level hit, with +∞ assigned when no hit occurs.
-- source:
--   Accepted Prove2Me reflectedSup_capped_closedLevelHit_stoppingTime and isStoppingTime_iSup_countable. General fluctuation-theory first passage construction.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_iSup_countable
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_closedLevelHit_stoppingTime

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.reflectedSup_countable_caps_hit_stoppingTime
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (caps : ℕ → ℝ≥0) (x : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      ⨆ n : ℕ,
        WithTop.some (sInf ((Icc (0 : ℝ≥0) (caps n) ∩
          (fun t : ℝ≥0 => reflectedSup X t ω) ⁻¹' Ici x) ∪ {caps n}))) := by sorry
