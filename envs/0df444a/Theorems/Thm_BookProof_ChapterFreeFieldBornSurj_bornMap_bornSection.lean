-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSurj_bornMap_bornSection
-- name    : BookProof.ChapterFreeFieldBornSurj.bornMap_bornSection
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T05:45:38.859801+00:00
-- url     : https://prove2.me/theorems/3efd4dab-415d-4292-9943-85d5b690d8e8
-- title:
--   `BookProof.ChapterFreeFieldBornSurj.bornMap_bornSection` {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) : bornMap (bornSection p) = p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSurj`.
--
--   `BookProof.ChapterFreeFieldBornSurj.bornMap_bornSection` {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) : bornMap (bornSection p) = p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSurj.bornMap_bornSection`.

-- Generated from ChapterFreeFieldBornSurj.lean — theorem BookProof.ChapterFreeFieldBornSurj.bornMap_bornSection
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Definitions.Def_ChapterFreeFieldBorn
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornSurj

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere
open BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn

theorem BookProof.ChapterFreeFieldBornSurj.bornMap_bornSection {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) :
    bornMap (bornSection p) = p := by sorry
