-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_normalized_binomialLogWeight_eq_binaryBarrierRate
-- name    : FirstPassageLinearTransport.normalized_binomialLogWeight_eq_binaryBarrierRate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:49.200794+00:00
-- url     : https://prove2.me/theorems/4d2fd6b1-0674-49ef-a273-1113abeb1fd4
-- title:
--   First Passage Linear Transport: normalized binomial Log Weight eq binary Barrier Rate
-- statement:
--   After dividing by the `2^r` Boolean mass, the Stirling exponential is
--   exactly the repository's binary barrier rate.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L374-L383
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L374-L383

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.normalized_binomialLogWeight_eq_binaryBarrierRate
    {r k : ℕ} (hk : 0 < k) (hkr : k < r) :
    binomialLogWeight r k - (r : ℝ) * Real.log 2 =
      -((r : ℝ) *
        binaryBarrierRate ((k : ℝ) / (r : ℝ) - 1 / 2)) := by sorry
