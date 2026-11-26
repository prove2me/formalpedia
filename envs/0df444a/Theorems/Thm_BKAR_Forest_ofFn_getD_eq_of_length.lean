-- Prove2me | Theorems.Thm_BKAR_Forest_ofFn_getD_eq_of_length
-- name    : BKAR.Forest.ofFn_getD_eq_of_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:13:20.798675+00:00
-- url     : https://prove2.me/theorems/7c972503-dba3-40a1-8d00-6c907c89f4c1
-- title:
--   Forest: of Fn get D eq of length
-- statement:
--   A list of the right length is recovered from its `getD` finite tuple.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L484-L491
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L484-L491

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.ofFn_getD_eq_of_length {n : ℕ} (ts : List ℝ)
    (hlen : ts.length = n) :
    List.ofFn (fun i : Fin n => ts.getD i.val 0) = ts := by sorry
