-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornCont_isCompact_stdSimplex_of_born
-- name    : BookProof.ChapterFreeFieldBornCont.isCompact_stdSimplex_of_born
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T06:32:27.308623+00:00
-- url     : https://prove2.me/theorems/a4caf03c-a1f6-4593-afcc-8b1d001760e6
-- title:
--   `BookProof.ChapterFreeFieldBornCont.isCompact_stdSimplex_of_born` : IsCompact (stdSimplex ℝ (Fin n))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornCont`.
--
--   `BookProof.ChapterFreeFieldBornCont.isCompact_stdSimplex_of_born` : IsCompact (stdSimplex ℝ (Fin n))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornCont.isCompact_stdSimplex_of_born`.

-- Generated from ChapterFreeFieldBornCont.lean — theorem BookProof.ChapterFreeFieldBornCont.isCompact_stdSimplex_of_born
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Mathlib
import Definitions.Def_ChapterFreeFieldBornCont
open BookProof.ChapterFreeFieldBornCont

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj

theorem BookProof.ChapterFreeFieldBornCont.isCompact_stdSimplex_of_born :
    IsCompact (stdSimplex ℝ (Fin n)) := by sorry
