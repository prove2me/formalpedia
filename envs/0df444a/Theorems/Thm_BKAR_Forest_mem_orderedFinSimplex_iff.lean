-- Prove2me | Theorems.Thm_BKAR_Forest_mem_orderedFinSimplex_iff
-- name    : BKAR.Forest.mem_orderedFinSimplex_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:57:40.512333+00:00
-- url     : https://prove2.me/theorems/45754b62-7a01-460e-b3ac-ba78cc055e64
-- title:
--   Forest: mem ordered Fin Simplex iff
-- statement:
--   The Forest construction uses the mem ordered Fin Simplex iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L205-L209
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean#L205-L209

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.mem_orderedFinSimplex_iff {n : ℕ} (ts : Fin n → ℝ) :
    ts ∈ orderedFinSimplex n ↔
      (∀ i, 0 ≤ ts i ∧ ts i ≤ 1) ∧
        OrderedSimplexParams 1 (List.ofFn ts) := by sorry
