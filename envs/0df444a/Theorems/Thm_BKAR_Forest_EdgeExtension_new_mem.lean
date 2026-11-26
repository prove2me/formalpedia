-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_new_mem
-- name    : BKAR.Forest.EdgeExtension.new_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:31.73368+00:00
-- url     : https://prove2.me/theorems/bc980b6d-6dbe-4b46-8afd-4731d0b98f4a
-- title:
--   Edge Extension: new mem
-- statement:
--   The Edge Extension construction uses the new mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L736-L738
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L736-L738

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

theorem BKAR.Forest.EdgeExtension.new_mem (h : EdgeExtension F F' e₀) : e₀ ∈ F'.edges := by sorry
