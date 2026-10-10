-- Prove2me | Theorems.Thm_BookProof_ChapterParity_antihermPart_isHermitian
-- name    : BookProof.ChapterParity.antihermPart_isHermitian
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:04:42.247988+00:00
-- url     : https://prove2.me/theorems/77215dde-2e6d-40f7-95ab-c5506713b3bd
-- title:
--   `BookProof.ChapterParity.antihermPart_isHermitian` (X : Matrix n n ℂ) : (antihermPart X).IsHermitian
-- statement:
--   Prove the following Lean 4 theorem from `ChapterParity`.
--
--   `BookProof.ChapterParity.antihermPart_isHermitian` (X : Matrix n n ℂ) : (antihermPart X).IsHermitian
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterParity.antihermPart_isHermitian`.

-- Generated from ChapterParity.lean — theorem BookProof.ChapterParity.antihermPart_isHermitian
import Mathlib
import Definitions.Def_ChapterParity
open BookProof.ChapterParity


open Matrix
open scoped ComplexConjugate

variable {n : Type*}

theorem BookProof.ChapterParity.antihermPart_isHermitian (X : Matrix n n ℂ) : (antihermPart X).IsHermitian := by sorry
