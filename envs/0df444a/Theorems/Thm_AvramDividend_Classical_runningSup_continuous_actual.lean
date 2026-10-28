-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
-- name    : AvramDividend.Classical.runningSup_continuous_actual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:44:42.728411+00:00
-- url     : https://prove2.me/theorems/20dd4d12-f613-47c3-acbc-9b2f0c0144e4
-- title:
--   The original spectrally negative Lévy running supremum is globally continuous on nonnegative real time
-- statement:
--   For every actual Lévy sample path, the running supremum S_t is continuous at every nonnegative time, including t=0. Apply the separately verified positive-time and origin continuity theorems in the two cases t>0 and t=0. In the excursion construction, this process S is the candidate normalized continuous additive local-time regulator at zero of reflected drawdown R=S−X. Global continuity is a genuine prerequisite for defining the inverse local-time subordinator and excursions as gaps of its inverse, but does not by itself prove the Poisson excursion measure or killed Markov law.
-- source:
--   Accepted runningSup_continuousAt_positive and runningSup_continuousAt_origin.

import Mathlib.Topology.ContinuousOn
import Theorems.Thm_AvramDividend_Classical_runningSup_continuousAt_positive
import Theorems.Thm_AvramDividend_Classical_runningSup_continuousAt_origin

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem AvramDividend.Classical.runningSup_continuous_actual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    Continuous (fun t : ℝ≥0 => runningSup X t ω) := by sorry
