-- Prove2me | Theorems.Thm_BookProof_ChapterA3m_swap23_kronecker
-- name    : BookProof.ChapterA3m.swap23_kronecker
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:00:35.299753+00:00
-- url     : https://prove2.me/theorems/fd14c96e-a4c2-4435-86bb-144e26d726e7
-- title:
--   `BookProof.ChapterA3m.swap23_kronecker` (A B C : Matrix (Fin 4) (Fin 4) ℂ) : swap23 * ((A ⊗ₖ B) ⊗ₖ C) = ((A ⊗ₖ C) ⊗ₖ B) * swap23
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3m`.
--
--   `BookProof.ChapterA3m.swap23_kronecker` (A B C : Matrix (Fin 4) (Fin 4) ℂ) : swap23 * ((A ⊗ₖ B) ⊗ₖ C) = ((A ⊗ₖ C) ⊗ₖ B) * swap23
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3m.swap23_kronecker`.

-- Generated from ChapterA3m.lean — theorem BookProof.ChapterA3m.swap23_kronecker
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3k
import Definitions.Def_ChapterA3l
import Mathlib
import Definitions.Def_ChapterA3m
open BookProof.ChapterA3m


open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3l

theorem BookProof.ChapterA3m.swap23_kronecker (A B C : Matrix (Fin 4) (Fin 4) ℂ) :
    swap23 * ((A ⊗ₖ B) ⊗ₖ C) = ((A ⊗ₖ C) ⊗ₖ B) * swap23 := by sorry
