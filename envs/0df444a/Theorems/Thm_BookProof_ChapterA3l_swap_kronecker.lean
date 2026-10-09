-- Prove2me | Theorems.Thm_BookProof_ChapterA3l_swap_kronecker
-- name    : BookProof.ChapterA3l.swap_kronecker
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:56:44.175479+00:00
-- url     : https://prove2.me/theorems/85ea1113-cb58-4753-8d9d-837f1d622158
-- title:
--   `BookProof.ChapterA3l.swap_kronecker` (A B : Matrix (Fin 4) (Fin 4) ℂ) : swap * (A ⊗ₖ B) = (B ⊗ₖ A) * swap
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3l`.
--
--   `BookProof.ChapterA3l.swap_kronecker` (A B : Matrix (Fin 4) (Fin 4) ℂ) : swap * (A ⊗ₖ B) = (B ⊗ₖ A) * swap
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3l.swap_kronecker`.

-- Generated from ChapterA3l.lean — theorem BookProof.ChapterA3l.swap_kronecker
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Mathlib
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3k
open BookProof.ChapterA3k
open BookProof.ChapterA3l


open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

theorem BookProof.ChapterA3l.swap_kronecker (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    swap * (A ⊗ₖ B) = (B ⊗ₖ A) * swap := by sorry
