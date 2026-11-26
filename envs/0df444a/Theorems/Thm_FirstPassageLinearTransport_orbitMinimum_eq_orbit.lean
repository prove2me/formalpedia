-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbitMinimum_eq_orbit
-- name    : FirstPassageLinearTransport.orbitMinimum_eq_orbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:55:58.922017+00:00
-- url     : https://prove2.me/theorems/af50e4d3-d64f-48cb-9638-96af64c4a90f
-- title:
--   First Passage Linear Transport: orbit Minimum eq orbit
-- statement:
--   The First Passage Linear Transport construction uses the orbit Minimum eq orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L72-L76
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L72-L76

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.orbitMinimum_eq_orbit (n : ℕ) :
    ∃ k : ℕ, orbitMinimum n = orbit k n := by sorry
