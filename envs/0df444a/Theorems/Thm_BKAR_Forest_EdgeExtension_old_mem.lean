-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_old_mem
-- name    : BKAR.Forest.EdgeExtension.old_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:29.807926+00:00
-- url     : https://prove2.me/theorems/4eee9a1b-60b6-4c4b-aad5-7a6093bd85f5
-- title:
--   Edge Extension: old mem
-- statement:
--   The Edge Extension construction uses the old mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L740-L743
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L740-L743

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
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e₀ e : Edge V}

theorem BKAR.Forest.EdgeExtension.old_mem (h : EdgeExtension F F' e₀) (he : e ∈ F.edges) :
    e ∈ F'.edges := by sorry
