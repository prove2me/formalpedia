-- Prove2me | Theorems.Thm_BookProof_ChapterA3k_chir2_spinGenDiag_comm
-- name    : BookProof.ChapterA3k.chir2_spinGenDiag_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T13:30:47.089865+00:00
-- url     : https://prove2.me/theorems/9109ce7a-a8ac-42ef-86e1-fc87b1224c8e
-- title:
--   `BookProof.ChapterA3k.chir2_spinGenDiag_comm` (μ ν : Fin 4) : chir2 * spinGenDiag μ ν = spinGenDiag μ ν * chir2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3k`.
--
--   `BookProof.ChapterA3k.chir2_spinGenDiag_comm` (μ ν : Fin 4) : chir2 * spinGenDiag μ ν = spinGenDiag μ ν * chir2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3k.chir2_spinGenDiag_comm`.

-- Generated from ChapterA3k.lean — theorem BookProof.ChapterA3k.chir2_spinGenDiag_comm
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA3k
import Definitions.Def_ChapterA3j
open BookProof.ChapterA3j
open BookProof.ChapterA3k


open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j

theorem BookProof.ChapterA3k.chir2_spinGenDiag_comm (μ ν : Fin 4) :
    chir2 * spinGenDiag μ ν = spinGenDiag μ ν * chir2 := by sorry
