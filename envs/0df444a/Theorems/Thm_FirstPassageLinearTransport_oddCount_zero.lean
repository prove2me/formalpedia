-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
-- name    : FirstPassageLinearTransport.oddCount_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:55:52.104802+00:00
-- url     : https://prove2.me/theorems/1e27be13-d103-40bb-8e17-e524ae263502
-- title:
--   First Passage Linear Transport: odd Count zero
-- statement:
--   The First Passage Linear Transport construction uses the odd Count zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L145-L146
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L145-L146

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.oddCount_zero (n : ℕ) : oddCount n 0 = 0 := by sorry
