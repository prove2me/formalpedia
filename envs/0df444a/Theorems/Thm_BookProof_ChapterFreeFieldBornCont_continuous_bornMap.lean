-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornCont_continuous_bornMap
-- name    : BookProof.ChapterFreeFieldBornCont.continuous_bornMap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T06:09:47.527273+00:00
-- url     : https://prove2.me/theorems/4298ffa4-17c9-48e5-887c-fa5df0bf1c27
-- title:
--   `BookProof.ChapterFreeFieldBornCont.continuous_bornMap` : Continuous (bornMap : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornCont`.
--
--   `BookProof.ChapterFreeFieldBornCont.continuous_bornMap` : Continuous (bornMap : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornCont.continuous_bornMap`.

-- Generated from ChapterFreeFieldBornCont.lean — theorem BookProof.ChapterFreeFieldBornCont.continuous_bornMap
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Mathlib
import Definitions.Def_ChapterFreeFieldBornCont
open BookProof.ChapterFreeFieldBornCont

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj

theorem BookProof.ChapterFreeFieldBornCont.continuous_bornMap :
    Continuous (bornMap : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) := by sorry
