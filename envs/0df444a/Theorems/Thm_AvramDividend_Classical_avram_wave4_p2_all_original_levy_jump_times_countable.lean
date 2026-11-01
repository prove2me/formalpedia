-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_all_original_levy_jump_times_countable
-- name    : AvramDividend.Classical.avram_wave4_p2_all_original_levy_jump_times_countable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:33:44.754987+00:00
-- url     : https://prove2.me/theorems/741d3b5f-bfd0-434e-846c-b274123b5ebe
-- title:
--   Every genuine spectrally negative Lévy sample path has countably many downward jump times, without a BV assumption
-- statement:
--   For the original X of an arbitrary actual spectrally negative Lévy process, not assuming bounded variation or Gaussianity and for every sample ω, all positive-time nonzero jump marks form a countable subset of NNReal. Every nonzero original jump is strictly downward by Proved e95fe5bc. A rational threshold between post-jump value and pre-jump left limit classifies it. For each rational threshold, the set of downward crossing times is isolated from the left within itself because the genuine left limit is above that threshold. Pinned Mathlib countable_setOfPred_isolated_left_within makes this crossing set countable; union over rational thresholds completes the proof. The theorem supplies the missing source-X jump-time countability for the 04-B atomless Stieltjes control identity e7696306, including UBV, without importing a compensator/Poisson law or claiming full Itô–Meyer.
-- source:
--   General deterministic càdlàg path regularity, original Avram SpectrallyNegativeLevy.leftLim and noPosJumps, Proved e95fe5bc-c756-43ca-82d7-acab7078e2eb; pinned Mathlib.Topology.Order.LeftRightNhds.countable_setOfPred_isolated_left_within.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_all_original_levy_jump_times_countable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    Set.Countable {t : ℝ≥0 |
      0 < t ∧ X.X t ω ≠ Function.leftLim
        (fun s : ℝ≥0 => X.X s ω) t} := by sorry
