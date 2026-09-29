-- Prove2me | Theorems.Thm_BookProof_ChapterParityMajoranaQuant_iJ_sq
-- name    : BookProof.ChapterParityMajoranaQuant.iJ_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:49:03.108653+00:00
-- url     : https://prove2.me/theorems/53c99e93-2eb4-4b20-bb70-2ae88707759e
-- title:
--   `iJ` is an involution: `(iJ)² = 1`, using `J² = -1`
-- statement:
--   `iJ` is an involution: `(iJ)² = 1`, using `J² = -1`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterParityMajoranaQuant.iJ_sq` (module `BookProof.ParityMajoranaQuant`), line-linked source: `ChapterParityMajoranaQuant.lean` lines 80–83.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParityMajoranaQuant.lean#L80-L83

-- Generated from ChapterParityMajoranaQuant.lean — theorem BookProof.ChapterParityMajoranaQuant.iJ_sq
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant










open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

theorem BookProof.ChapterParityMajoranaQuant.iJ_sq (hJ2 : J * J = -1) : iJ J * iJ J = 1 := by sorry
