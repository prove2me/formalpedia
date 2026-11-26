-- Prove2me | Theorems.Thm_BKAR_Forest_orderedFinSimplexWithTop_subset_pi_Icc
-- name    : BKAR.Forest.orderedFinSimplexWithTop_subset_pi_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:29.552116+00:00
-- url     : https://prove2.me/theorems/42aa5cea-6a3b-482e-99c2-471dbce56821
-- title:
--   Forest: ordered Fin Simplex With Top subset pi Icc
-- statement:
--   A variable-top finite ordered simplex is contained in the coordinate box `[0, top]^n`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L147-L158
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L147-L158

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedFinSimplexWithTop_subset_pi_Icc (top : ℝ) (n : ℕ) :
    orderedFinSimplexWithTop top n ⊆
      Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) top := by sorry
