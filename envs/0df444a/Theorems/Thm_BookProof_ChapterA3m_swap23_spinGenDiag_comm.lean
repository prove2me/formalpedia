-- Prove2me | Theorems.Thm_BookProof_ChapterA3m_swap23_spinGenDiag_comm
-- name    : BookProof.ChapterA3m.swap23_spinGenDiag_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:06:07.408354+00:00
-- url     : https://prove2.me/theorems/fc643a14-625a-4e71-b8e5-2dc4a416285d
-- title:
--   `BookProof.ChapterA3m.swap23_spinGenDiag_comm` (μ ν : Fin 4) : swap23 * spinGenDiag3 μ ν = spinGenDiag3 μ ν * swap23
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3m`.
--
--   `BookProof.ChapterA3m.swap23_spinGenDiag_comm` (μ ν : Fin 4) : swap23 * spinGenDiag3 μ ν = spinGenDiag3 μ ν * swap23
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3m.swap23_spinGenDiag_comm`.

-- Generated from ChapterA3m.lean — theorem BookProof.ChapterA3m.swap23_spinGenDiag_comm
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3k
import Definitions.Def_ChapterA3l
import Mathlib
import Definitions.Def_ChapterA3m
import Definitions.Def_ChapterA3j
open BookProof.ChapterA3j
open BookProof.ChapterA3m


open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3l

theorem BookProof.ChapterA3m.swap23_spinGenDiag_comm (μ ν : Fin 4) :
    swap23 * spinGenDiag3 μ ν = spinGenDiag3 μ ν * swap23 := by sorry
