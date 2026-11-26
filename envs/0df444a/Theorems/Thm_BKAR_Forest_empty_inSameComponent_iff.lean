-- Prove2me | Theorems.Thm_BKAR_Forest_empty_inSameComponent_iff
-- name    : BKAR.Forest.empty_inSameComponent_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:14.618725+00:00
-- url     : https://prove2.me/theorems/8dbd564d-b0c7-4483-af09-fc81504b93a5
-- title:
--   Forest: empty in Same Component iff
-- statement:
--   The Forest construction uses the empty in Same Component iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L608-L610
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L608-L610

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

theorem BKAR.Forest.empty_inSameComponent_iff {i j : V} :
    (empty V).inSameComponent i j ↔ i = j := by sorry
