-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornCont_continuous_bornSection
-- name    : BookProof.ChapterFreeFieldBornCont.continuous_bornSection
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T06:10:16.126349+00:00
-- url     : https://prove2.me/theorems/1d95dc27-a659-4d2d-af69-88067bc9d5b1
-- title:
--   `BookProof.ChapterFreeFieldBornCont.continuous_bornSection` : Continuous (bornSection : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornCont`.
--
--   `BookProof.ChapterFreeFieldBornCont.continuous_bornSection` : Continuous (bornSection : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornCont.continuous_bornSection`.

-- Generated from ChapterFreeFieldBornCont.lean — theorem BookProof.ChapterFreeFieldBornCont.continuous_bornSection
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Mathlib
import Definitions.Def_ChapterFreeFieldBornCont
open BookProof.ChapterFreeFieldBornCont

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj

theorem BookProof.ChapterFreeFieldBornCont.continuous_bornSection :
    Continuous (bornSection : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) := by sorry
