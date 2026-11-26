-- Prove2me | Theorems.Thm_BKAR_Forest_activeDirection_apply_of_mem
-- name    : BKAR.Forest.activeDirection_apply_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:20:12.673272+00:00
-- url     : https://prove2.me/theorems/4f92e203-9b6a-45d4-9a7d-034cc241f189
-- title:
--   Forest: active Direction apply of mem
-- statement:
--   The Forest construction uses the active Direction apply of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L96-L107
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L96-L107

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.activeDirection_apply_of_mem (F : Forest V) {e : Edge V}
    (he : e ∈ F.activeEdges) :
    F.activeDirection e = 1 := by sorry
