-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
-- name    : FirstPassageLinearTransport.parityBit_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:55:54.022823+00:00
-- url     : https://prove2.me/theorems/b4936305-84b4-52a3-b34a-c50b700a95b4
-- title:
--   First Passage Linear Transport: parity Bit zero
-- statement:
--   The First Passage Linear Transport construction uses the parity Bit zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L139-L140
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L139-L140

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.parityBit_zero (n : ℕ) : (parityBit n 0 : ℕ) = n % 2 := by sorry
