-- Prove2me | Theorems.Thm_Comp_coin_ne_zero_iff
-- name    : Comp.coin_ne_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:56:31.939535+00:00
-- url     : https://prove2.me/theorems/c6c99658-8dc0-4d2c-98cd-b69f3230d018
-- title:
--   Comp: coin ne zero iff
-- statement:
--   The coin's support is the pair it mixes -- for the qualitative operators, the only thing about
--       it that matters. Note that the *weights* are irrelevant to everything downstream: replacing
--       `1/2` by any other pair of positive rationals changes nothing below.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L139-L142
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L139-L142

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.coin_ne_zero_iff (t u s' : Chain) : coin t u s' ≠ 0 ↔ s' = t ∨ s' = u := by sorry
