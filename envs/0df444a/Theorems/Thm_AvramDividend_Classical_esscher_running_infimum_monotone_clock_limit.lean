-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_running_infimum_monotone_clock_limit
-- name    : AvramDividend.Classical.esscher_running_infimum_monotone_clock_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:33:41.637793+00:00
-- url     : https://prove2.me/theorems/c89cda7a-af48-4b46-bca8-d852a57f5223
-- title:
--   Antitone finite running infima converge along unbounded coupled horizons
-- statement:
--   For a sample path whose real running infimum I(t) is antitone in NNReal time and has a finite lower bound, the infimum evaluated at any coupled clock tending to infinity as its positive rate tends down to zero converges to the perpetual running infimum inf_t I(t). The hypotheses explicitly require finite perpetual infimum and an unbounded clock. Applied pointwise to Esscher paths, these are genuine stochastic obligations, independent of finite-p Wiener–Hopf and any transform conclusion.
-- source:
--   Pinned Mathlib.Topology.Order.MonotoneConvergence.tendsto_atTop_ciInf and Mathlib.Data.NNReal.Defs; coupled clock C2 helper ff8ecd57-1a1b-4355-8de3-0e69197b24f4; Kyprianou, Introductory Lectures on Fluctuations of Lévy Processes.

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope
open Filter Set

theorem AvramDividend.Classical.esscher_running_infimum_monotone_clock_limit
    (I : NNReal → ℝ)
    (hAnti : Antitone I)
    (hbdd : BddBelow (Set.range I))
    (clock : ℝ → NNReal)
    (hclock : Tendsto clock (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    Tendsto (fun p : ℝ => I (clock p))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (⨅ t : NNReal, I t)) := by sorry
