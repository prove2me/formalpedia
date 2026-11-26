-- Prove2me | Theorems.Thm_BKAR_Forest_isCompact_orderedFinSimplexWithTop
-- name    : BKAR.Forest.isCompact_orderedFinSimplexWithTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:10:59.150973+00:00
-- url     : https://prove2.me/theorems/73457773-6962-555a-ac78-f29466542c98
-- title:
--   Forest: is Compact ordered Fin Simplex With Top
-- statement:
--   Variable-top finite ordered simplexes are compact.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L162-L169
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L162-L169

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.isCompact_orderedFinSimplexWithTop (top : ℝ) (n : ℕ) :
    IsCompact (orderedFinSimplexWithTop top n) := by sorry
