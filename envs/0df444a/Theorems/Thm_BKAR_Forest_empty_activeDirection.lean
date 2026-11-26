-- Prove2me | Theorems.Thm_BKAR_Forest_empty_activeDirection
-- name    : BKAR.Forest.empty_activeDirection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:24:39.702411+00:00
-- url     : https://prove2.me/theorems/41e5db71-17da-5c14-ae41-327e8a15fe2c
-- title:
--   Forest: empty active Direction
-- statement:
--   The Forest construction uses the empty active Direction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L121-L127
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L121-L127

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.empty_activeDirection :
    (Forest.empty V).activeDirection = oneConfig := by sorry
