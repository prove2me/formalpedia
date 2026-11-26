-- Prove2me | Theorems.Thm_BKAR_IsAcyclicEdgeSet_mono
-- name    : BKAR.IsAcyclicEdgeSet.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:18.804825+00:00
-- url     : https://prove2.me/theorems/46f26e92-75c4-4d86-8499-358346e4cc27
-- title:
--   Is Acyclic Edge Set: mono
-- statement:
--   Acyclicity is inherited by finite edge subsets.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L312-L352
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L312-L352

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
set_option autoImplicit false
open BKAR
open BKAR.IsAcyclicEdgeSet
variable {V} [Fintype V] [DecidableEq V]

theorem BKAR.IsAcyclicEdgeSet.mono {S T : Finset (Edge V)}
    (hS : IsAcyclicEdgeSet S) (hsub : T ⊆ S) :
    IsAcyclicEdgeSet T := by sorry
