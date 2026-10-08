-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSectionBij_mem_nonnegOrthant
-- name    : BookProof.ChapterFreeFieldBornSectionBij.mem_nonnegOrthant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T06:57:06.863594+00:00
-- url     : https://prove2.me/theorems/1f77a98c-d2ee-48d9-8e6e-0fda625d470d
-- title:
--   `BookProof.ChapterFreeFieldBornSectionBij.mem_nonnegOrthant` {x : EuclideanSpace ℝ (Fin n)} : x ∈ nonnegOrthant n ↔ ∀ k, 0 ≤ x k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSectionBij`.
--
--   `BookProof.ChapterFreeFieldBornSectionBij.mem_nonnegOrthant` {x : EuclideanSpace ℝ (Fin n)} : x ∈ nonnegOrthant n ↔ ∀ k, 0 ≤ x k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSectionBij.mem_nonnegOrthant`.

-- Generated from ChapterFreeFieldBornSectionBij.lean — theorem BookProof.ChapterFreeFieldBornSectionBij.mem_nonnegOrthant
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSectionBij
open BookProof.ChapterFreeFieldBornSectionBij

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere
open BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSurj

theorem BookProof.ChapterFreeFieldBornSectionBij.mem_nonnegOrthant {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ nonnegOrthant n ↔ ∀ k, 0 ≤ x k := by sorry
