-- Prove2me | Theorems.Thm_BookProof_ChapterParityHiggs_higgsReal_mul_conj
-- name    : BookProof.ChapterParityHiggs.higgsReal_mul_conj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:07:07.801538+00:00
-- url     : https://prove2.me/theorems/e7d90f9b-7ade-431f-b522-8a2ed19061f9
-- title:
--   `BookProof.ChapterParityHiggs.higgsReal_mul_conj` : higgsReal * (higgsReal.map (starRingEnd ℂ)) = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterParityHiggs`.
--
--   `BookProof.ChapterParityHiggs.higgsReal_mul_conj` : higgsReal * (higgsReal.map (starRingEnd ℂ)) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterParityHiggs.higgsReal_mul_conj`.

-- Generated from ChapterParityHiggs.lean — theorem BookProof.ChapterParityHiggs.higgsReal_mul_conj
import Mathlib
import Definitions.Def_ChapterParityHiggs
import Definitions.Def_ChapterParity
open BookProof.ChapterParity
open BookProof.ChapterParityHiggs


open Matrix
open scoped Kronecker
open scoped ComplexConjugate


open BookProof.ChapterParity

theorem BookProof.ChapterParityHiggs.higgsReal_mul_conj : higgsReal * (higgsReal.map (starRingEnd ℂ)) = 1 := by sorry
