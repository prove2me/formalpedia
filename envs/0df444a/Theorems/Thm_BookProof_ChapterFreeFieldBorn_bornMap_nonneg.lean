-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBorn_bornMap_nonneg
-- name    : BookProof.ChapterFreeFieldBorn.bornMap_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T05:01:16.832893+00:00
-- url     : https://prove2.me/theorems/271d0826-0859-45d7-b411-56dda2538f7f
-- title:
--   `BookProof.ChapterFreeFieldBorn.bornMap_nonneg` (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) : 0 ≤ bornMap x k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBorn`.
--
--   `BookProof.ChapterFreeFieldBorn.bornMap_nonneg` (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) : 0 ≤ bornMap x k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBorn.bornMap_nonneg`.

-- Generated from ChapterFreeFieldBorn.lean — theorem BookProof.ChapterFreeFieldBorn.bornMap_nonneg
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

theorem BookProof.ChapterFreeFieldBorn.bornMap_nonneg (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) : 0 ≤ bornMap x k := by sorry
