-- Prove2me | Theorems.Thm_BKAR_Forest_mem_orderedCubeSimplex_iff
-- name    : BKAR.Forest.mem_orderedCubeSimplex_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:46:13.085904+00:00
-- url     : https://prove2.me/theorems/0e272102-b18f-4d2e-94f5-ee2b8217cd51
-- title:
--   Forest: mem ordered Cube Simplex iff
-- statement:
--   The Forest construction uses the mem ordered Cube Simplex iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L48-L53
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean#L48-L53

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.mem_orderedCubeSimplex_iff
    (F : Forest V) (order : List (Edge V)) (u : F.EdgeParam → ℝ) :
    u ∈ F.orderedCubeSimplex order ↔
      u ∈ F.unitCube ∧
        OrderedSimplexParams 1 (order.map (F.paramValue u)) := by sorry
