-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbit_add
-- name    : FirstPassageLinearTransport.orbit_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:56:18.967394+00:00
-- url     : https://prove2.me/theorems/54ea1326-bbcd-5c3f-95d3-dd346da9bc44
-- title:
--   First Passage Linear Transport: orbit add
-- statement:
--   The First Passage Linear Transport construction uses the orbit add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L129-L130
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L129-L130

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.orbit_add (j k n : ℕ) : orbit (j + k) n = orbit j (orbit k n) := by sorry
