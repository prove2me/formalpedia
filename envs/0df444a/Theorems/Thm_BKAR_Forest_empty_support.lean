-- Prove2me | Theorems.Thm_BKAR_Forest_empty_support
-- name    : BKAR.Forest.empty_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:09.790743+00:00
-- url     : https://prove2.me/theorems/8bcdeedb-45d4-45bb-8ef4-14e5f0f5f70c
-- title:
--   Forest: empty support
-- statement:
--   The Forest construction uses the empty support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L600-L602
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L600-L602

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

theorem BKAR.Forest.empty_support :
    (empty V).support = ⟨∅, ⟨emptyAcyclicEdgeSetData⟩⟩ := by sorry
