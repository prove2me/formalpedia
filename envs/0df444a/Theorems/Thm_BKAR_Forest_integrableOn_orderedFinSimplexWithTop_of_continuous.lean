-- Prove2me | Theorems.Thm_BKAR_Forest_integrableOn_orderedFinSimplexWithTop_of_continuous
-- name    : BKAR.Forest.integrableOn_orderedFinSimplexWithTop_of_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:38.332954+00:00
-- url     : https://prove2.me/theorems/c8183a38-fa9e-49a0-a8c5-6b58b70670d3
-- title:
--   Forest: integrable On ordered Fin Simplex With Top of continuous
-- statement:
--   Continuous functions are integrable on variable-top finite ordered simplexes.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L173-L177
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L173-L177

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.integrableOn_orderedFinSimplexWithTop_of_continuous
    {top : ℝ} {n : ℕ} {G : (Fin n → ℝ) → ℝ}
    (hG : Continuous G) :
    IntegrableOn G (orderedFinSimplexWithTop top n) := by sorry
