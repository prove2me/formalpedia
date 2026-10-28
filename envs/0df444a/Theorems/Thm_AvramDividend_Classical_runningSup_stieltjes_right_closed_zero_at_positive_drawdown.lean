-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_stieltjes_right_closed_zero_at_positive_drawdown
-- name    : AvramDividend.Classical.runningSup_stieltjes_right_closed_zero_at_positive_drawdown
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:52:48.146972+00:00
-- url     : https://prove2.me/theorems/790bb38c-8e59-4f35-8d7f-2831dabfbe97
-- title:
--   Continuous running-record local time assigns zero mass to an entire right-closed neighbourhood beginning at any time of positive reflected drawdown
-- statement:
--   For each sample path of the genuine reflected spectrally negative Lévy process, at every time u where the drawdown R_u is positive, the actual running-record Stieltjes regulator measure dS vanishes on some nondegenerate interval [u,v]. The established right-open interval support lemma gives dS((u,v])=0; the independently proved no-atoms theorem gives dS({u})=0, and subadditivity implies dS([u,v])=0. This is a stronger genuine excursion local-time support statement, including the possible instantaneous jump-entry time u. Combined with a suitable countable covering theorem for the positive-drawdown set, it will establish that the regulator/local-time measure is supported on zero-reflection times, which is central to defining an Itô excursion point process and its intensity n.
-- source:
--   Accepted runningSup_stieltjes_right_interval_zero_at_positive_drawdown and runningSup_dividendMeasure_no_real_atoms.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Theorems.Thm_AvramDividend_Classical_runningSup_stieltjes_right_interval_zero_at_positive_drawdown
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_real_atoms

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_stieltjes_right_closed_zero_at_positive_drawdown
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u : ℝ≥0)
    (hPositive : 0 < reflectedSup X u ω) :
    ∃ v : ℝ≥0, u < v ∧
      (dividendMeasure (runningSup X) ω)
        (Set.Icc (u : ℝ) (v : ℝ)) = 0 := by sorry
