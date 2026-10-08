-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSectionBij_bornSection_bornMap
-- name    : BookProof.ChapterFreeFieldBornSectionBij.bornSection_bornMap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T07:14:14.982308+00:00
-- url     : https://prove2.me/theorems/9500c6ca-39dd-4bf0-b440-4c35b15b86ae
-- title:
--   `BookProof.ChapterFreeFieldBornSectionBij.bornSection_bornMap` {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ nonnegOrthant n) : bornSection (bornMap x) = x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSectionBij`.
--
--   `BookProof.ChapterFreeFieldBornSectionBij.bornSection_bornMap` {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ nonnegOrthant n) : bornSection (bornMap x) = x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSectionBij.bornSection_bornMap`.

-- Generated from ChapterFreeFieldBornSectionBij.lean — theorem BookProof.ChapterFreeFieldBornSectionBij.bornSection_bornMap
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

theorem BookProof.ChapterFreeFieldBornSectionBij.bornSection_bornMap {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ nonnegOrthant n) :
    bornSection (bornMap x) = x := by sorry
