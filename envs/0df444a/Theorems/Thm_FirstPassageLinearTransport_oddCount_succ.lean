-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_oddCount_succ
-- name    : FirstPassageLinearTransport.oddCount_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:55:58.059513+00:00
-- url     : https://prove2.me/theorems/67676b01-7e20-4009-a185-a975e3a8b4d9
-- title:
--   First Passage Linear Transport: odd Count succ
-- statement:
--   The First Passage Linear Transport construction uses the odd Count succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L148-L150
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Basic.lean#L148-L150

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Nat
import Definitions.Def_FirstPassageLinearTransport_Basic
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.oddCount_succ (n k : ℕ) :
    oddCount n (k + 1) = oddCount n k + (parityBit n k : ℕ) := by sorry
