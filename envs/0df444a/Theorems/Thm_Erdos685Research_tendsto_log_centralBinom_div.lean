-- Prove2me | Theorems.Thm_Erdos685Research_tendsto_log_centralBinom_div
-- name    : Erdos685Research.tendsto_log_centralBinom_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:41:27.178786+00:00
-- url     : https://prove2.me/theorems/248b84fa-d202-5426-8976-4d84f9a30547
-- title:
--   Erdos685 Research: tendsto log central Binom div
-- statement:
--   The logarithm of the central binomial coefficient has exponential rate `log 4`.
--
--   Source: https://github.com/AItoBit/erdos-685-elementary-lower-bound/blob/c8618095373664c5c8ea35f78304abdd4ec41691/Asymptotic/CentralGrowth.lean#L21-L53
-- source:
--   https://github.com/AItoBit/erdos-685-elementary-lower-bound/blob/c8618095373664c5c8ea35f78304abdd4ec41691/Asymptotic/CentralGrowth.lean#L21-L53

module
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Definitions.Def_Asymptotic_CentralGrowth
set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos685Research

theorem Erdos685Research.tendsto_log_centralBinom_div :
    Tendsto (fun n : ℕ => Real.log (Nat.centralBinom n : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 4)) := by sorry
