-- Prove2me | Theorems.Thm_BKAR_Forest_activeDirection_apply_of_not_mem
-- name    : BKAR.Forest.activeDirection_apply_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:21:25.149644+00:00
-- url     : https://prove2.me/theorems/24afdfe2-5df0-4cd9-8226-d53e15d27b6c
-- title:
--   Forest: active Direction apply of not mem
-- statement:
--   The Forest construction uses the active Direction apply of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L109-L119
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L109-L119

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.activeDirection_apply_of_not_mem (F : Forest V) {e : Edge V}
    (he : e ∉ F.activeEdges) :
    F.activeDirection e = 0 := by sorry
