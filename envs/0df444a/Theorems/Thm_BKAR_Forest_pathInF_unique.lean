-- Prove2me | Theorems.Thm_BKAR_Forest_pathInF_unique
-- name    : BKAR.Forest.pathInF_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:14.680316+00:00
-- url     : https://prove2.me/theorems/58fc4b54-1ce8-4f07-a32c-343a43a80408
-- title:
--   Forest: path In F unique
-- statement:
--   Lemma A1: the simple path in a forest is unique.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L656-L660
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L656-L660

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

theorem BKAR.Forest.pathInF_unique (F : Forest V) {i j : V}
    (h : F.inSameComponent i j) (γ : List (Edge V))
    (hγ : IsSimplePath F γ i j) :
    γ = F.pathInF i j h := by sorry
