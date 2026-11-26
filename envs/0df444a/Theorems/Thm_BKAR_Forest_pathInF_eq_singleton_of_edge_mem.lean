-- Prove2me | Theorems.Thm_BKAR_Forest_pathInF_eq_singleton_of_edge_mem
-- name    : BKAR.Forest.pathInF_eq_singleton_of_edge_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:20.671787+00:00
-- url     : https://prove2.me/theorems/0a5e32c6-75fb-570f-a671-605136aea088
-- title:
--   Forest: path In F eq singleton of edge mem
-- statement:
--   The Forest construction uses the path In F eq singleton of edge mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L662-L665
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L662-L665

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

theorem BKAR.Forest.pathInF_eq_singleton_of_edge_mem (F : Forest V) {e : Edge V}
    (he : e ∈ F.edges) :
    F.pathInF e.left e.right (F.edge_inSameComponent he) = [e] := by sorry
