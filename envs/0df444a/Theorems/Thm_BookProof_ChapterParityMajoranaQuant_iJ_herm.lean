-- Prove2me | Theorems.Thm_BookProof_ChapterParityMajoranaQuant_iJ_herm
-- name    : BookProof.ChapterParityMajoranaQuant.iJ_herm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:48:19.735049+00:00
-- url     : https://prove2.me/theorems/238bb0ac-019a-4c82-99fc-3e477e08ff06
-- title:
--   `iJ` is Hermitian: `(iJ)ᴴ = iJ`, using skew-adjointness `Jᴴ = -J` and `conj i = -i`
-- statement:
--   `iJ` is Hermitian: `(iJ)ᴴ = iJ`, using skew-adjointness `Jᴴ = -J` and `conj i = -i`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterParityMajoranaQuant.iJ_herm` (module `BookProof.ParityMajoranaQuant`), line-linked source: `ChapterParityMajoranaQuant.lean` lines 75–78.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParityMajoranaQuant.lean#L75-L78

-- Generated from ChapterParityMajoranaQuant.lean — theorem BookProof.ChapterParityMajoranaQuant.iJ_herm
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant










open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

theorem BookProof.ChapterParityMajoranaQuant.iJ_herm (hskew : Jᴴ = -J) : (iJ J)ᴴ = iJ J := by sorry
