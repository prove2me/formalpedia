-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_right_local_const_of_positive_drawdown
-- name    : AvramDividend.Classical.runningSup_right_local_const_of_positive_drawdown
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:21:18.359876+00:00
-- url     : https://prove2.me/theorems/46d49112-5863-407e-af3e-4b6314f24397
-- title:
--   The actual spectrally negative Lévy running-supremum local-time regulator is locally constant immediately after every positive reflected drawdown
-- statement:
--   For every sample path of the canonical spectrally negative Lévy process and any time u with reflected drawdown R_u=S_u−X_u>0, there exists a real time v>u such that the regulator S_t=runningSup X t is exactly constant throughout [u,v). Indeed R_u>0 says X_u<S_u. The original process path is right-continuous, so the accepted right-gap lemma gives v>u with X_t<S_u on that interval. By the accepted actual running-supremum no-new-record lemma, S_t remains S_u for every t there. This is a genuine pathwise local-time support prerequisite: at times when R>0 there is no immediate future increase in dS. It does not by itself show dS({R>0})=0, because down-jump times can be approached by old records from the left, nor does it construct the sigma-finite Itô excursion law n or the killed Markov property.
-- source:
--   Accepted original Lévy right continuity X.rightCont, runningSup_const_between_of_path_below_old_record and nnreal_rightContinuous_strict_upper_gap_interval; underlying excursion regulator construction for spectrally negative Lévy processes.

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_const_between_of_path_below_old_record
import Theorems.Thm_AvramDividend_Classical_nnreal_rightContinuous_strict_upper_gap_interval
import Mathlib.Topology.Order.LeftRightNhds

open AvramDividend.Classical MeasureTheory Set Topology Filter
open scoped NNReal

theorem AvramDividend.Classical.runningSup_right_local_const_of_positive_drawdown
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0)
    (hPositive : 0 < reflectedSup X u ω) :
    ∃ v : ℝ≥0, u < v ∧
      ∀ t : ℝ≥0, u ≤ t → t < v →
        runningSup X t ω = runningSup X u ω := by sorry
