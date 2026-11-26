-- Prove2me | Theorems.Thm_BKAR_Forest_inSameComponent_trans
-- name    : BKAR.Forest.inSameComponent_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:04:59.840858+00:00
-- url     : https://prove2.me/theorems/1ad9183f-9ab0-4b0b-b231-63f4e7cee8a1
-- title:
--   Forest: in Same Component trans
-- statement:
--   The Forest construction uses the in Same Component trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ForestGraph.lean#L409-L413
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/ForestGraph.lean#L409-L413

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_ForestGraph
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.inSameComponent_trans (F : Forest V)
    {i j k : V} (hij : F.inSameComponent i j)
    (hjk : F.inSameComponent j k) :
    F.inSameComponent i k := by sorry
