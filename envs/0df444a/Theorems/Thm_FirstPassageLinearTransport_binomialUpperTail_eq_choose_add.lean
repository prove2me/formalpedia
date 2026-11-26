-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_binomialUpperTail_eq_choose_add
-- name    : FirstPassageLinearTransport.binomialUpperTail_eq_choose_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:20:34.878513+00:00
-- url     : https://prove2.me/theorems/7a9c8272-3b9a-4165-9ec8-bd340061bc26
-- title:
--   First Passage Linear Transport: binomial Upper Tail eq choose add
-- statement:
--   Removing the first binomial layer from a nonempty upper tail.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L127-L132
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpEntropyBarrier.lean#L127-L132

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

theorem FirstPassageLinearTransport.binomialUpperTail_eq_choose_add
    {r k : ℕ} (hkr : k ≤ r) :
    binomialUpperTail r k = r.choose k + binomialUpperTail r (k + 1) := by sorry
