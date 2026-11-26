-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_mem_old_of_mem_of_ne
-- name    : BKAR.Forest.EdgeExtension.mem_old_of_mem_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:33.211847+00:00
-- url     : https://prove2.me/theorems/d98718ba-b723-4d16-9f73-62780a857b0c
-- title:
--   Edge Extension: mem old of mem of ne
-- statement:
--   The Edge Extension construction uses the mem old of mem of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L745-L751
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L745-L751

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

theorem BKAR.Forest.EdgeExtension.mem_old_of_mem_of_ne (h : EdgeExtension F F' e₀)
    (he : e ∈ F'.edges) (hne : e ≠ e₀) : e ∈ F.edges := by sorry
