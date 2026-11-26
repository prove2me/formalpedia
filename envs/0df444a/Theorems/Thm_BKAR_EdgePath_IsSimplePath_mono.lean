-- Prove2me | Theorems.Thm_BKAR_EdgePath_IsSimplePath_mono
-- name    : BKAR.EdgePath.IsSimplePath.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:14.024202+00:00
-- url     : https://prove2.me/theorems/0c1bd3f7-ade4-5cfb-a4e2-2da616c3708c
-- title:
--   Is Simple Path: mono
-- statement:
--   The Is Simple Path construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L188-L192
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L188-L192

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

theorem BKAR.EdgePath.IsSimplePath.mono {S T : Finset (Edge V)} (hsub : S ⊆ T)
    {γ : List (Edge V)} {i j : V}
    (h : IsSimplePath S γ i j) :
    IsSimplePath T γ i j := by sorry
