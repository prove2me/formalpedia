-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_binomialLogWeight_eq_mul_binEntropy
-- name    : FirstPassageLinearTransport.binomialLogWeight_eq_mul_binEntropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:43.683651+00:00
-- url     : https://prove2.me/theorems/8fcfb1a7-db1f-4f07-98ae-002e0e8be130
-- title:
--   First Passage Linear Transport: binomial Log Weight eq mul bin Entropy
-- statement:
--   The logarithmic Stirling weight is exactly `r` times binary entropy at the
--   empirical success proportion `k / r`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L351-L370
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L351-L370

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

theorem FirstPassageLinearTransport.binomialLogWeight_eq_mul_binEntropy
    {r k : ℕ} (hk : 0 < k) (hkr : k < r) :
    binomialLogWeight r k =
      (r : ℝ) * Real.binEntropy ((k : ℝ) / (r : ℝ)) := by sorry
