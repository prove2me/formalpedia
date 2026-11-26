-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shortcut_of_odd
-- name    : FirstPassageLinearTransport.shortcut_of_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:55:58.676691+00:00
-- url     : https://prove2.me/theorems/2dd009b6-210c-5f24-a250-6c9465abfe42
-- title:
--   First Passage Linear Transport: shortcut of odd
-- statement:
--   The First Passage Linear Transport construction uses the shortcut of odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L108-L110
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L108-L110

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.shortcut_of_odd {n : ℕ} (hn : n % 2 = 1) :
    shortcut n = (3 * n + 1) / 2 := by sorry
