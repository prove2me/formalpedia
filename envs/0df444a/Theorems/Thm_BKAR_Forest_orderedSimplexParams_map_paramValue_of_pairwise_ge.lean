-- Prove2me | Theorems.Thm_BKAR_Forest_orderedSimplexParams_map_paramValue_of_pairwise_ge
-- name    : BKAR.Forest.orderedSimplexParams_map_paramValue_of_pairwise_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:49:41.120361+00:00
-- url     : https://prove2.me/theorems/fe56e98a-12c3-415c-b8da-867b2d47c150
-- title:
--   Forest: ordered Simplex Params map param Value of pairwise ge
-- statement:
--   If an edge order is pairwise sorted in descending parameter value and every
--   listed value lies in `[0, top]`, then the readback value list is an ordered
--   simplex.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L171-L194
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L171-L194

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedSimplexParams_map_paramValue_of_pairwise_ge
    (F : Forest V) (u : F.EdgeParam → ℝ) :
    ∀ (order : List (Edge V)) (top : ℝ),
      order.Pairwise (fun e e' => F.paramValue u e' ≤ F.paramValue u e) →
      (∀ e ∈ order, 0 ≤ F.paramValue u e) →
      (∀ e ∈ order, F.paramValue u e ≤ top) →
      OrderedSimplexParams top (order.map (F.paramValue u))
  := by sorry
