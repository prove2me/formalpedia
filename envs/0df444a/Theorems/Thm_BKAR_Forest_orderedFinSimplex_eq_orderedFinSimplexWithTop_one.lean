-- Prove2me | Theorems.Thm_BKAR_Forest_orderedFinSimplex_eq_orderedFinSimplexWithTop_one
-- name    : BKAR.Forest.orderedFinSimplex_eq_orderedFinSimplexWithTop_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:33.519795+00:00
-- url     : https://prove2.me/theorems/8d99c4bb-c898-4047-8db4-868d9eaa4741
-- title:
--   Forest: ordered Fin Simplex eq ordered Fin Simplex With Top one
-- statement:
--   The original finite sector is the variable-top simplex with top `1`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L181-L195
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L181-L195

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedFinSimplex_eq_orderedFinSimplexWithTop_one (n : ℕ) :
    orderedFinSimplex n = orderedFinSimplexWithTop 1 n := by sorry
