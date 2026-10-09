-- Prove2me | Theorems.Thm_BookProof_ChapterA3l_projAsym_spinGenDiag_comm
-- name    : BookProof.ChapterA3l.projAsym_spinGenDiag_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:59:39.379405+00:00
-- url     : https://prove2.me/theorems/80598ca9-7dab-4c66-a125-87e3c6dcc8cd
-- title:
--   `BookProof.ChapterA3l.projAsym_spinGenDiag_comm` (μ ν : Fin 4) : projAsym * spinGenDiag μ ν = spinGenDiag μ ν * projAsym
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3l`.
--
--   `BookProof.ChapterA3l.projAsym_spinGenDiag_comm` (μ ν : Fin 4) : projAsym * spinGenDiag μ ν = spinGenDiag μ ν * projAsym
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3l.projAsym_spinGenDiag_comm`.

-- Generated from ChapterA3l.lean — theorem BookProof.ChapterA3l.projAsym_spinGenDiag_comm
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

theorem BookProof.ChapterA3l.projAsym_spinGenDiag_comm (μ ν : Fin 4) :
    projAsym * spinGenDiag μ ν = spinGenDiag μ ν * projAsym := by sorry
