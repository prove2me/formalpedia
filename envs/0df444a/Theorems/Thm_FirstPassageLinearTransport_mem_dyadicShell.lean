-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
-- name    : FirstPassageLinearTransport.mem_dyadicShell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:55:54.546833+00:00
-- url     : https://prove2.me/theorems/d9172cfd-9341-4eb9-8843-3b015e069bc5
-- title:
--   First Passage Linear Transport: mem dyadic Shell
-- statement:
--   The First Passage Linear Transport construction uses the mem dyadic Shell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L153-L155
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L153-L155

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.mem_dyadicShell {M n : ℕ} :
    n ∈ dyadicShell M ↔ 2 ^ M ≤ n ∧ n < 2 ^ (M + 1) := by sorry
