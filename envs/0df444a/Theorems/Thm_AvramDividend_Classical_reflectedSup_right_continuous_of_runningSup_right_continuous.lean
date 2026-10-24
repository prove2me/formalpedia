-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_right_continuous_of_runningSup_right_continuous
-- name    : AvramDividend.Classical.reflectedSup_right_continuous_of_runningSup_right_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T10:48:55.371445+00:00
-- url     : https://prove2.me/theorems/e8e0a450-7995-44ba-9bfe-608d6bd890a0
-- title:
--   Right continuity of reflected Lévy drawdown from the running record path
-- statement:
--   For a spectrally negative Lévy process with right-continuous sample paths, if its running supremum process is right-continuous at time u, then the reflected drawdown runningSup X_t − X_t is also right-continuous at u. This is the right-continuity prerequisite for showing strict reflected ruin cannot coincide with a new finite record contact when barrier a>0. It is a purely pathwise continuity transfer, not a strong Markov property or a stochastic barrier valuation.
-- source:
--   Avram, Palmowski, Pistorius (2007) §3.3 reflected supremum Y⁺=S−X, and Lean module Definition Reflection; continuity of subtraction with X.rightCont.

import Definitions.Def_AvramDividend_Classical_Reflection

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.reflectedSup_right_continuous_of_runningSup_right_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0)
    (hSup : ContinuousWithinAt (fun t : ℝ≥0 => runningSup X t ω)
      (Set.Ici u) u) :
    ContinuousWithinAt (fun t : ℝ≥0 => reflectedSup X t ω)
      (Set.Ici u) u := by sorry
