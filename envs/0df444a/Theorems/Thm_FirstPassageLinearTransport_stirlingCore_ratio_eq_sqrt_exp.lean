-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stirlingCore_ratio_eq_sqrt_exp
-- name    : FirstPassageLinearTransport.stirlingCore_ratio_eq_sqrt_exp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:20:24.58592+00:00
-- url     : https://prove2.me/theorems/c3c13b32-b9b9-5efe-8dc2-d4fa5e8eede7
-- title:
--   First Passage Linear Transport: stirling Core ratio eq sqrt exp
-- statement:
--   The First Passage Linear Transport construction uses the stirling Core ratio eq sqrt exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L247-L272
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L247-L272

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

theorem FirstPassageLinearTransport.stirlingCore_ratio_eq_sqrt_exp
    {r k : ℕ} (hk : 0 < k) (hkr : k < r) :
    stirlingCore r / (stirlingCore k * stirlingCore (r - k)) =
      Real.sqrt (2 * r) /
          (Real.sqrt (2 * k) * Real.sqrt (2 * (r - k))) *
        Real.exp (binomialLogWeight r k) := by sorry
