-- Prove2me | Theorems.Thm_BKAR_Edge_mk_comm
-- name    : BKAR.Edge.mk_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:49.631161+00:00
-- url     : https://prove2.me/theorems/28c826b0-21fa-52b1-8fd6-315b659d8deb
-- title:
--   Edge: mk comm
-- statement:
--   The Edge construction uses the mk comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L56-L59
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L56-L59

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

theorem BKAR.Edge.mk_comm (i j : V) (hij : i ≠ j) :
    mk i j hij = mk j i hij.symm := by sorry
