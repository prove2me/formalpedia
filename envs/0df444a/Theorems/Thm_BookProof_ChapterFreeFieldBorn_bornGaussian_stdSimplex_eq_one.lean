-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBorn_bornGaussian_stdSimplex_eq_one
-- name    : BookProof.ChapterFreeFieldBorn.bornGaussian_stdSimplex_eq_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T05:21:57.037578+00:00
-- url     : https://prove2.me/theorems/4a9d5f37-ef7c-4534-b6ee-1325f3dc6f00
-- title:
--   `BookProof.ChapterFreeFieldBorn.bornGaussian_stdSimplex_eq_one` (hn : 0 < n) : ((sphereGaussian n).map bornMap) (stdSimplex ℝ (Fin n)) = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBorn`.
--
--   `BookProof.ChapterFreeFieldBorn.bornGaussian_stdSimplex_eq_one` (hn : 0 < n) : ((sphereGaussian n).map bornMap) (stdSimplex ℝ (Fin n)) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBorn.bornGaussian_stdSimplex_eq_one`.

-- Generated from ChapterFreeFieldBorn.lean — theorem BookProof.ChapterFreeFieldBorn.bornGaussian_stdSimplex_eq_one
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Mathlib
import Definitions.Def_ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBorn

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere
open BookProof.ChapterFreeFieldSphereSupport

theorem BookProof.ChapterFreeFieldBorn.bornGaussian_stdSimplex_eq_one (hn : 0 < n) :
    ((sphereGaussian n).map bornMap) (stdSimplex ℝ (Fin n)) = 1 := by sorry
