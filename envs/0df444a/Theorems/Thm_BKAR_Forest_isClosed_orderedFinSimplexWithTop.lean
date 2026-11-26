-- Prove2me | Theorems.Thm_BKAR_Forest_isClosed_orderedFinSimplexWithTop
-- name    : BKAR.Forest.isClosed_orderedFinSimplexWithTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:35.997603+00:00
-- url     : https://prove2.me/theorems/93b30407-227e-4981-b6d7-c409c8affa39
-- title:
--   Forest: is Closed ordered Fin Simplex With Top
-- statement:
--   Variable-top finite ordered simplexes are closed.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L127-L143
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L127-L143

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.isClosed_orderedFinSimplexWithTop (top : ℝ) (n : ℕ) :
    IsClosed (orderedFinSimplexWithTop top n) := by sorry
