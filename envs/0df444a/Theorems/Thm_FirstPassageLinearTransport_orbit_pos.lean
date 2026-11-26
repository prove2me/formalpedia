-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbit_pos
-- name    : FirstPassageLinearTransport.orbit_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:56:20.632349+00:00
-- url     : https://prove2.me/theorems/e747c9ff-7bf1-57e4-af5e-b372e2a10e36
-- title:
--   First Passage Linear Transport: orbit pos
-- statement:
--   The First Passage Linear Transport construction uses the orbit pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L132-L137
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L132-L137

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.orbit_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < orbit k n := by sorry
