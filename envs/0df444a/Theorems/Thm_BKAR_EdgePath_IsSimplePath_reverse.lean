-- Prove2me | Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
-- name    : BKAR.EdgePath.IsSimplePath.reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:18.868295+00:00
-- url     : https://prove2.me/theorems/d3a8737d-fef5-4a12-84e3-30162ef99924
-- title:
--   Is Simple Path: reverse
-- statement:
--   The Is Simple Path construction uses the reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L207-L211
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L207-L211

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
set_option autoImplicit false
open BKAR
open BKAR.EdgePath
variable {V} [DecidableEq V]
open BKAR.EdgePath.IsSimplePath

theorem BKAR.EdgePath.IsSimplePath.reverse {S : Finset (Edge V)}
    {γ : List (Edge V)} {i j : V}
    (h : IsSimplePath S γ i j) :
    IsSimplePath S γ.reverse j i := by sorry
