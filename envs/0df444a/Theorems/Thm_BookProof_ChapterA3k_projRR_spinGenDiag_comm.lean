-- Prove2me | Theorems.Thm_BookProof_ChapterA3k_projRR_spinGenDiag_comm
-- name    : BookProof.ChapterA3k.projRR_spinGenDiag_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T13:31:20.483876+00:00
-- url     : https://prove2.me/theorems/084ec5f6-9e71-4328-ac85-9efe42b19219
-- title:
--   `BookProof.ChapterA3k.projRR_spinGenDiag_comm` (μ ν : Fin 4) : projRR * spinGenDiag μ ν = spinGenDiag μ ν * projRR
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3k`.
--
--   `BookProof.ChapterA3k.projRR_spinGenDiag_comm` (μ ν : Fin 4) : projRR * spinGenDiag μ ν = spinGenDiag μ ν * projRR
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3k.projRR_spinGenDiag_comm`.

-- Generated from ChapterA3k.lean — theorem BookProof.ChapterA3k.projRR_spinGenDiag_comm
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA3k
import Definitions.Def_ChapterA3j
open BookProof.ChapterA3j
open BookProof.ChapterA3k


open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j

theorem BookProof.ChapterA3k.projRR_spinGenDiag_comm (μ ν : Fin 4) :
    projRR * spinGenDiag μ ν = spinGenDiag μ ν * projRR := by sorry
