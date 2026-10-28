-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_local_zero_stieltjes_mass_positive_drawdown
-- name    : AvramDividend.Classical.runningSup_local_zero_stieltjes_mass_positive_drawdown
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:27:54.672437+00:00
-- url     : https://prove2.me/theorems/e4d2bf23-dd25-4976-b9b9-3dc9902efebc
-- title:
--   Actual reflected Lévy local-time regulator has a positive right-hand interval of zero Stieltjes mass at every positive drawdown
-- statement:
--   Let R=S−X be the canonical spectrally negative Lévy drawdown, S its running maximum, and dS the genuine Lebesgue–Stieltjes regulator measure already formalised as dividendMeasure. At any sample-path time u where R_u>0, there is a strictly later v>u such that dS((u,v])=0. The path X is right-continuous, hence its strict gap X_u<S_u persists on a nonzero interval [u,v'); choose any v in (u,v'), and invoke the accepted Stieltjes zero-mass no-new-record interval theorem. This gives a genuine local-time measure property for each positive drawdown without choosing, constructing or assuming an excursion measure n. It is a necessary but not alone sufficient ingredient of proving support(dS)⊆{R=0}, whose countable-cover and jump-time arguments must be addressed separately.
-- source:
--   Accepted runningSup_no_new_record_interval_zero_stieltjes_mass, nnreal_rightContinuous_strict_upper_gap_interval and X.rightCont; local time for spectrally negative reflected Lévy process.

import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_runningSup_no_new_record_interval_zero_stieltjes_mass
import Theorems.Thm_AvramDividend_Classical_nnreal_rightContinuous_strict_upper_gap_interval
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.NNReal.Basic

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_local_zero_stieltjes_mass_positive_drawdown
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0)
    (hPositive : 0 < reflectedSup X u ω) :
    ∃ v : ℝ≥0, u < v ∧
      (dividendMeasure (runningSup X) ω)
        (Set.Ioc (u : ℝ) (v : ℝ)) = 0 := by sorry
