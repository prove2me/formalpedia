-- Prove2me | Theorems.Thm_BKAR_Forest_acyclic_insert_iff
-- name    : BKAR.Forest.acyclic_insert_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:48.017962+00:00
-- url     : https://prove2.me/theorems/e2e9c36a-35e2-5d55-ac3b-a1f803022f8f
-- title:
--   Forest: acyclic insert iff
-- statement:
--   Lemma A2: adding an absent edge preserves acyclicity exactly across components.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L708-L714
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L708-L714

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

theorem BKAR.Forest.acyclic_insert_iff (F : Forest V) {i j : V} (hij : i ≠ j)
    (he : Edge.mk i j hij ∉ F.edges) :
    IsAcyclicEdgeSet (insert (Edge.mk i j hij) F.edges) ↔
      ¬ F.inSameComponent i j := by sorry
