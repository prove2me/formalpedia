-- Prove2me | Theorems.Thm_BKAR_Forest_paramsOfOrder_continuous_of_listPathContinuous
-- name    : BKAR.Forest.paramsOfOrder_continuous_of_listPathContinuous
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:05:15.270492+00:00
-- url     : https://prove2.me/theorems/a4378149-4d42-43ba-a519-cdd57f8e65eb
-- title:
--   Forest: params Of Order continuous of list Path Continuous
-- statement:
--   The Forest construction uses the params Of Order continuous of list Path Continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Smoothness.lean#L19-L26
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Smoothness.lean#L19-L26

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_Smoothness
import Definitions.Def_BKAR_CubePartition_Smoothness
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.paramsOfOrder_continuous_of_listPathContinuous
    (F : Forest V) (order : List (Edge V))
    {X : Type*} [TopologicalSpace X] {n : Nat} {tsPath : X → List ℝ}
    (hts : BKAR.ListPathContinuous n tsPath) :
    Continuous (fun x : X => F.paramsOfOrder order (tsPath x)) := by sorry
