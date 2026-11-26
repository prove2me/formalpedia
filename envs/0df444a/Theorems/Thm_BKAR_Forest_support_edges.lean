-- Prove2me | Theorems.Thm_BKAR_Forest_support_edges
-- name    : BKAR.Forest.support_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:06.142963+00:00
-- url     : https://prove2.me/theorems/85afb001-f7e3-4877-bcb5-68936453c949
-- title:
--   Forest: support edges
-- statement:
--   The Forest construction uses the support edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L596-L598
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L596-L598

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.support_edges (F : Forest V) :
    F.support.edges = F.edges := by sorry
