-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSurj_bornSection_apply
-- name    : BookProof.ChapterFreeFieldBornSurj.bornSection_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T05:44:33.677782+00:00
-- url     : https://prove2.me/theorems/480113db-e4b1-4715-b54d-3ccd9b5b5338
-- title:
--   `BookProof.ChapterFreeFieldBornSurj.bornSection_apply` (p : Fin n → ℝ) (k : Fin n) : bornSection p k = Real.sqrt (p k)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSurj`.
--
--   `BookProof.ChapterFreeFieldBornSurj.bornSection_apply` (p : Fin n → ℝ) (k : Fin n) : bornSection p k = Real.sqrt (p k)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSurj.bornSection_apply`.

-- Generated from ChapterFreeFieldBornSurj.lean — theorem BookProof.ChapterFreeFieldBornSurj.bornSection_apply
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

theorem BookProof.ChapterFreeFieldBornSurj.bornSection_apply (p : Fin n → ℝ) (k : Fin n) :
    bornSection p k = Real.sqrt (p k) := by sorry
