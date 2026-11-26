-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbit_zero
-- name    : FirstPassageLinearTransport.orbit_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:55:51.694387+00:00
-- url     : https://prove2.me/theorems/23f42d31-913e-527a-b96f-1cc7390021ee
-- title:
--   First Passage Linear Transport: orbit zero
-- statement:
--   The First Passage Linear Transport construction uses the orbit zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L123-L124
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L123-L124

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.orbit_zero (n : ℕ) : orbit 0 n = n := by sorry
