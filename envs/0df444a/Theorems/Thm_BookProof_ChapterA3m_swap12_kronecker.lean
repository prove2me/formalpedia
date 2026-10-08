-- Prove2me | Theorems.Thm_BookProof_ChapterA3m_swap12_kronecker
-- name    : BookProof.ChapterA3m.swap12_kronecker
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:00:34.01549+00:00
-- url     : https://prove2.me/theorems/6d40c6ac-cc83-45de-9f94-e5bc53ab38ee
-- title:
--   `BookProof.ChapterA3m.swap12_kronecker` (A B C : Matrix (Fin 4) (Fin 4) ℂ) : swap12 * ((A ⊗ₖ B) ⊗ₖ C) = ((B ⊗ₖ A) ⊗ₖ C) * swap12
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3m`.
--
--   `BookProof.ChapterA3m.swap12_kronecker` (A B C : Matrix (Fin 4) (Fin 4) ℂ) : swap12 * ((A ⊗ₖ B) ⊗ₖ C) = ((B ⊗ₖ A) ⊗ₖ C) * swap12
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3m.swap12_kronecker`.

-- Generated from ChapterA3m.lean — theorem BookProof.ChapterA3m.swap12_kronecker
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Mathlib
import Definitions.Def_ChapterA3m
import Definitions.Def_ChapterA3k
import Definitions.Def_ChapterA3l
open BookProof.ChapterA3k
open BookProof.ChapterA3l
open BookProof.ChapterA3m


open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3l

theorem BookProof.ChapterA3m.swap12_kronecker (A B C : Matrix (Fin 4) (Fin 4) ℂ) :
    swap12 * ((A ⊗ₖ B) ⊗ₖ C) = ((B ⊗ₖ A) ⊗ₖ C) * swap12 := by sorry
