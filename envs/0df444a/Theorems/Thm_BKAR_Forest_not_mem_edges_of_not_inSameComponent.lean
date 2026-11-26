-- Prove2me | Theorems.Thm_BKAR_Forest_not_mem_edges_of_not_inSameComponent
-- name    : BKAR.Forest.not_mem_edges_of_not_inSameComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:20:56.962287+00:00
-- url     : https://prove2.me/theorems/4cb15152-3dbb-48e1-bc45-902f5ce2cefd
-- title:
--   Forest: not mem edges of not in Same Component
-- statement:
--   The Forest construction uses the not mem edges of not in Same Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L62-L66
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L62-L66

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.not_mem_edges_of_not_inSameComponent (F : Forest V) {e : Edge V}
    (he : ¬ F.inSameComponent e.left e.right) :
    e ∉ F.edges := by sorry
