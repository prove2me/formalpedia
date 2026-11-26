-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbitMinimum_le_iff_reachesBelow
-- name    : FirstPassageLinearTransport.orbitMinimum_le_iff_reachesBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:56:15.015668+00:00
-- url     : https://prove2.me/theorems/4e7e9e38-d4dd-446d-a479-72cb052b7ba2
-- title:
--   First Passage Linear Transport: orbit Minimum le iff reaches Below
-- statement:
--   The First Passage Linear Transport construction uses the orbit Minimum le iff reaches Below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L78-L88
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L78-L88

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.orbitMinimum_le_iff_reachesBelow {n : ℕ} {Y : ℝ} :
    (orbitMinimum n : ℝ) ≤ Y ↔ ReachesBelow n Y := by sorry
