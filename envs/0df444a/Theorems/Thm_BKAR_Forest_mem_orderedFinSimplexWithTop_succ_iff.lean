-- Prove2me | Theorems.Thm_BKAR_Forest_mem_orderedFinSimplexWithTop_succ_iff
-- name    : BKAR.Forest.mem_orderedFinSimplexWithTop_succ_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:56.763033+00:00
-- url     : https://prove2.me/theorems/1de01947-e34c-40a4-a35c-f7a97cbf5022
-- title:
--   Forest: mem ordered Fin Simplex With Top succ iff
-- statement:
--   Head-tail membership characterization for the variable-top finite simplex.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L199-L208
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L199-L208

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem BKAR.Forest.mem_orderedFinSimplexWithTop_succ_iff
    (top : ℝ) {n : ℕ} (ts : Fin (n + 1) → ℝ) :
    ts ∈ orderedFinSimplexWithTop top (n + 1) ↔
      0 ≤ ts 0 ∧ ts 0 ≤ top ∧
        Fin.tail ts ∈ orderedFinSimplexWithTop (ts 0) n := by sorry
