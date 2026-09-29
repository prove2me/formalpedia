-- Prove2me | Theorems.Thm_BookProof_ChapterParityMajoranaQuant_stdJ_skew
-- name    : BookProof.ChapterParityMajoranaQuant.stdJ_skew
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:50:05.854608+00:00
-- url     : https://prove2.me/theorems/05231cb7-bb4d-438e-b440-923e341513fa
-- title:
--   The standard symplectic unit is skew-adjoint `stdJᴴ = -stdJ` (real skew-symmetric)
-- statement:
--   The standard symplectic unit is skew-adjoint `stdJᴴ = -stdJ` (real skew-symmetric).
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterParityMajoranaQuant.stdJ_skew` (module `BookProof.ParityMajoranaQuant`), line-linked source: `ChapterParityMajoranaQuant.lean` lines 187–190.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParityMajoranaQuant.lean#L187-L190

-- Generated from ChapterParityMajoranaQuant.lean — theorem BookProof.ChapterParityMajoranaQuant.stdJ_skew
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant










open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

theorem BookProof.ChapterParityMajoranaQuant.stdJ_skew : stdJᴴ = -stdJ := by sorry
