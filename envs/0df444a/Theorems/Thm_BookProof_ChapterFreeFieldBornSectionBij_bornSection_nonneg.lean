-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSectionBij_bornSection_nonneg
-- name    : BookProof.ChapterFreeFieldBornSectionBij.bornSection_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T06:57:32.484816+00:00
-- url     : https://prove2.me/theorems/fed4353c-b35f-4224-84ab-5be9146a24da
-- title:
--   `BookProof.ChapterFreeFieldBornSectionBij.bornSection_nonneg` (p : Fin n → ℝ) : bornSection p ∈ nonnegOrthant n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSectionBij`.
--
--   `BookProof.ChapterFreeFieldBornSectionBij.bornSection_nonneg` (p : Fin n → ℝ) : bornSection p ∈ nonnegOrthant n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSectionBij.bornSection_nonneg`.

-- Generated from ChapterFreeFieldBornSectionBij.lean — theorem BookProof.ChapterFreeFieldBornSectionBij.bornSection_nonneg
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

theorem BookProof.ChapterFreeFieldBornSectionBij.bornSection_nonneg (p : Fin n → ℝ) : bornSection p ∈ nonnegOrthant n := by sorry
