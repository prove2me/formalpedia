-- Prove2me | Theorems.Thm_BookProof_ChapterA3k_chir1_spinGenDiag_comm
-- name    : BookProof.ChapterA3k.chir1_spinGenDiag_comm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:56:18.59241+00:00
-- url     : https://prove2.me/theorems/57d9ad3c-0f42-4072-956c-a4f81b9e020f
-- title:
--   `BookProof.ChapterA3k.chir1_spinGenDiag_comm` (μ ν : Fin 4) : chir1 * spinGenDiag μ ν = spinGenDiag μ ν * chir1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3k`.
--
--   `BookProof.ChapterA3k.chir1_spinGenDiag_comm` (μ ν : Fin 4) : chir1 * spinGenDiag μ ν = spinGenDiag μ ν * chir1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3k.chir1_spinGenDiag_comm`.

-- Generated from ChapterA3k.lean — theorem BookProof.ChapterA3k.chir1_spinGenDiag_comm
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA3k
import Definitions.Def_ChapterA3j
open BookProof.ChapterA3j
open BookProof.ChapterA3k


open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j

theorem BookProof.ChapterA3k.chir1_spinGenDiag_comm (μ ν : Fin 4) :
    chir1 * spinGenDiag μ ν = spinGenDiag μ ν * chir1 := by sorry
