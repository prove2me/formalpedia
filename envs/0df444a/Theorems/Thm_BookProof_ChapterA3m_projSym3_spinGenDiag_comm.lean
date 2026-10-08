-- Prove2me | Theorems.Thm_BookProof_ChapterA3m_projSym3_spinGenDiag_comm
-- name    : BookProof.ChapterA3m.projSym3_spinGenDiag_comm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:07:11.925981+00:00
-- url     : https://prove2.me/theorems/dda5bb9d-e896-4470-b511-acd4361248c9
-- title:
--   `BookProof.ChapterA3m.projSym3_spinGenDiag_comm` (μ ν : Fin 4) : projSym3 * spinGenDiag3 μ ν = spinGenDiag3 μ ν * projSym3
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3m`.
--
--   `BookProof.ChapterA3m.projSym3_spinGenDiag_comm` (μ ν : Fin 4) : projSym3 * spinGenDiag3 μ ν = spinGenDiag3 μ ν * projSym3
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3m.projSym3_spinGenDiag_comm`.

-- Generated from ChapterA3m.lean — theorem BookProof.ChapterA3m.projSym3_spinGenDiag_comm
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

theorem BookProof.ChapterA3m.projSym3_spinGenDiag_comm (μ ν : Fin 4) :
    projSym3 * spinGenDiag3 μ ν = spinGenDiag3 μ ν * projSym3 := by sorry
