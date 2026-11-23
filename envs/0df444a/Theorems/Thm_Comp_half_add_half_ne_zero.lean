-- Prove2me | Theorems.Thm_Comp_half_add_half_ne_zero
-- name    : Comp.half_add_half_ne_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:56:21.68716+00:00
-- url     : https://prove2.me/theorems/8fd1e84f-9d12-493c-a076-32ad45cc191f
-- title:
--   Comp: half add half ne zero
-- statement:
--   A nonnegative combination with positive weights vanishes only if both parts do. Isolated as its
--       own arithmetic lemma because it is the only place the coin's *numbers* are reasoned about.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L118-L134
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L118-L134

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.half_add_half_ne_zero {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 / 2 * a + 1 / 2 * b ≠ 0 ↔ a ≠ 0 ∨ b ≠ 0 := by sorry
