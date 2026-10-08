-- Prove2me | Theorems.Thm_BookProof_ChapterA3l_swap_spinGenDiag_comm
-- name    : BookProof.ChapterA3l.swap_spinGenDiag_comm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:57:14.247215+00:00
-- url     : https://prove2.me/theorems/18c42c35-33fc-4fa1-bef3-55696eabc91c
-- title:
--   `BookProof.ChapterA3l.swap_spinGenDiag_comm` (μ ν : Fin 4) : swap * spinGenDiag μ ν = spinGenDiag μ ν * swap
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3l`.
--
--   `BookProof.ChapterA3l.swap_spinGenDiag_comm` (μ ν : Fin 4) : swap * spinGenDiag μ ν = spinGenDiag μ ν * swap
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3l.swap_spinGenDiag_comm`.

-- Generated from ChapterA3l.lean — theorem BookProof.ChapterA3l.swap_spinGenDiag_comm
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3k
open BookProof.ChapterA3j
open BookProof.ChapterA3k
open BookProof.ChapterA3l


open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

theorem BookProof.ChapterA3l.swap_spinGenDiag_comm (μ ν : Fin 4) :
    swap * spinGenDiag μ ν = spinGenDiag μ ν * swap := by sorry
