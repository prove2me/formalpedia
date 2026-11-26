-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shortcut_of_even
-- name    : FirstPassageLinearTransport.shortcut_of_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:55:59.154879+00:00
-- url     : https://prove2.me/theorems/10bad1fe-7e18-4c41-bb5b-9c94d44353a4
-- title:
--   First Passage Linear Transport: shortcut of even
-- statement:
--   The First Passage Linear Transport construction uses the shortcut of even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L104-L106
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L104-L106

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.shortcut_of_even {n : ℕ} (hn : n % 2 = 0) :
    shortcut n = n / 2 := by sorry
