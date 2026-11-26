-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_parityBit_lt_two
-- name    : FirstPassageLinearTransport.parityBit_lt_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:56:42.962963+00:00
-- url     : https://prove2.me/theorems/67fbaf43-088d-54bf-9971-ac4d8b62e5f1
-- title:
--   First Passage Linear Transport: parity Bit lt two
-- statement:
--   The First Passage Linear Transport construction uses the parity Bit lt two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L142-L143
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L142-L143

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.parityBit_lt_two (n i : ℕ) : (parityBit n i : ℕ) < 2 := by sorry
