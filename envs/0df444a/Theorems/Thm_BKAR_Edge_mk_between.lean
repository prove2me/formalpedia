-- Prove2me | Theorems.Thm_BKAR_Edge_mk_between
-- name    : BKAR.Edge.mk_between
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:32.57626+00:00
-- url     : https://prove2.me/theorems/efb8ce38-e710-4e77-a509-5940da8f21d8
-- title:
--   Edge: mk between
-- statement:
--   The Edge construction uses the mk between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L53-L54
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L53-L54

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

theorem BKAR.Edge.mk_between (i j : V) (hij : i ≠ j) : (mk i j hij).Between i j := by sorry
