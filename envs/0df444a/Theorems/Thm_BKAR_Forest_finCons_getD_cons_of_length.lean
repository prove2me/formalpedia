-- Prove2me | Theorems.Thm_BKAR_Forest_finCons_getD_cons_of_length
-- name    : BKAR.Forest.finCons_getD_cons_of_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:12:29.647357+00:00
-- url     : https://prove2.me/theorems/51396192-1b74-5b87-942a-54661346a15a
-- title:
--   Forest: fin Cons get D cons of length
-- statement:
--   A consed list, read through `getD`, is the corresponding `Fin.cons` tuple.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L495-L511
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L495-L511

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.finCons_getD_cons_of_length {n : ℕ} (t : ℝ) (ts : List ℝ)
    (hlen : ts.length = n) :
    (fun i : Fin (n + 1) => (t :: ts).getD i.val 0) =
      Fin.cons t (fun i : Fin n => ts.getD i.val 0) := by sorry
