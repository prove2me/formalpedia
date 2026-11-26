-- Prove2me | Theorems.Thm_BKAR_Edge_left_ne_right
-- name    : BKAR.Edge.left_ne_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:52.27867+00:00
-- url     : https://prove2.me/theorems/666046c8-405b-43e0-82b4-e53f5fef5c6c
-- title:
--   Edge: left ne right
-- statement:
--   The Edge construction uses the left ne right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L77-L81
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L77-L81

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
set_option autoImplicit false
open BKAR
open BKAR.Edge
variable {V} [DecidableEq V]

theorem BKAR.Edge.left_ne_right (e : Edge V) : e.left ≠ e.right := by sorry
