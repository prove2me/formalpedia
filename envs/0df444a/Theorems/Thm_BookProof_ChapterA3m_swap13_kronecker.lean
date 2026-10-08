-- Prove2me | Theorems.Thm_BookProof_ChapterA3m_swap13_kronecker
-- name    : BookProof.ChapterA3m.swap13_kronecker
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:00:44.209504+00:00
-- url     : https://prove2.me/theorems/5b2a312e-31a2-48fa-a17c-5ce9214e36bb
-- title:
--   `BookProof.ChapterA3m.swap13_kronecker` (A B C : Matrix (Fin 4) (Fin 4) ℂ) : swap13 * ((A ⊗ₖ B) ⊗ₖ C) = ((C ⊗ₖ B) ⊗ₖ A) * swap13
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3m`.
--
--   `BookProof.ChapterA3m.swap13_kronecker` (A B C : Matrix (Fin 4) (Fin 4) ℂ) : swap13 * ((A ⊗ₖ B) ⊗ₖ C) = ((C ⊗ₖ B) ⊗ₖ A) * swap13
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3m.swap13_kronecker`.

-- Generated from ChapterA3m.lean — theorem BookProof.ChapterA3m.swap13_kronecker
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

theorem BookProof.ChapterA3m.swap13_kronecker (A B C : Matrix (Fin 4) (Fin 4) ℂ) :
    swap13 * ((A ⊗ₖ B) ⊗ₖ C) = ((C ⊗ₖ B) ⊗ₖ A) * swap13 := by sorry
