-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbit_succ
-- name    : FirstPassageLinearTransport.orbit_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:55:55.290371+00:00
-- url     : https://prove2.me/theorems/3dc7b4d4-6cb1-5a37-9d5d-f6a39999875c
-- title:
--   First Passage Linear Transport: orbit succ
-- statement:
--   The First Passage Linear Transport construction uses the orbit succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L126-L127
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L126-L127

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.orbit_succ (k n : ℕ) : orbit (k + 1) n = shortcut (orbit k n) := by sorry
