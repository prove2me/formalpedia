-- Prove2me | Theorems.Thm_BKAR_Edge_not_isDiag
-- name    : BKAR.Edge.not_isDiag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:48.032946+00:00
-- url     : https://prove2.me/theorems/e9e86b19-1468-4766-9e23-a81d8d6c039b
-- title:
--   Edge: not is Diag
-- statement:
--   The Edge construction uses the not is Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L46-L47
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L46-L47

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

theorem BKAR.Edge.not_isDiag (e : Edge V) : ¬ e.val.IsDiag := by sorry
