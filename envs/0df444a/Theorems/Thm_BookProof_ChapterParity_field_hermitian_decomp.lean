-- Prove2me | Theorems.Thm_BookProof_ChapterParity_field_hermitian_decomp
-- name    : BookProof.ChapterParity.field_hermitian_decomp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:04:35.256059+00:00
-- url     : https://prove2.me/theorems/9a2436fa-b49f-4bb3-94ff-3053006f345b
-- title:
--   `BookProof.ChapterParity.field_hermitian_decomp` (X : Matrix n n ℂ) : X = hermPart X + Complex.I • antihermPart X
-- statement:
--   Prove the following Lean 4 theorem from `ChapterParity`.
--
--   `BookProof.ChapterParity.field_hermitian_decomp` (X : Matrix n n ℂ) : X = hermPart X + Complex.I • antihermPart X
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterParity.field_hermitian_decomp`.

-- Generated from ChapterParity.lean — theorem BookProof.ChapterParity.field_hermitian_decomp
import Mathlib
import Definitions.Def_ChapterParity
open BookProof.ChapterParity


open Matrix
open scoped ComplexConjugate

variable {n : Type*}

theorem BookProof.ChapterParity.field_hermitian_decomp (X : Matrix n n ℂ) :
    X = hermPart X + Complex.I • antihermPart X := by sorry
