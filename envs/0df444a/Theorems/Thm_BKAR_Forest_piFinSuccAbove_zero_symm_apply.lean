-- Prove2me | Theorems.Thm_BKAR_Forest_piFinSuccAbove_zero_symm_apply
-- name    : BKAR.Forest.piFinSuccAbove_zero_symm_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:39:34.140141+00:00
-- url     : https://prove2.me/theorems/03fb5620-8f6d-5da9-9042-723054ad3682
-- title:
--   Forest: pi Fin Succ Above zero symm apply
-- statement:
--   At coordinate `0`, the inverse head-tail split is just `Fin.cons`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L380-L392
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L380-L392

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.piFinSuccAbove_zero_symm_apply
    {n : ℕ} (t : ℝ) (us : Fin n → ℝ) :
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) 0).symm (t, us) =
      Fin.cons t us := by sorry
