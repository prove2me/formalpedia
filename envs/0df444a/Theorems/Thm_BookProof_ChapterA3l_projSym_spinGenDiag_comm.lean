-- Prove2me | Theorems.Thm_BookProof_ChapterA3l_projSym_spinGenDiag_comm
-- name    : BookProof.ChapterA3l.projSym_spinGenDiag_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:59:13.977976+00:00
-- url     : https://prove2.me/theorems/b419a18f-d7f4-47ff-9201-1ffd7556764d
-- title:
--   `BookProof.ChapterA3l.projSym_spinGenDiag_comm` (μ ν : Fin 4) : projSym * spinGenDiag μ ν = spinGenDiag μ ν * projSym
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3l`.
--
--   `BookProof.ChapterA3l.projSym_spinGenDiag_comm` (μ ν : Fin 4) : projSym * spinGenDiag μ ν = spinGenDiag μ ν * projSym
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3l.projSym_spinGenDiag_comm`.

-- Generated from ChapterA3l.lean — theorem BookProof.ChapterA3l.projSym_spinGenDiag_comm
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

theorem BookProof.ChapterA3l.projSym_spinGenDiag_comm (μ ν : Fin 4) :
    projSym * spinGenDiag μ ν = spinGenDiag μ ν * projSym := by sorry
