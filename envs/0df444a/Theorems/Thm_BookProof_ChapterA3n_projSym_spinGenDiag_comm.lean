-- Prove2me | Theorems.Thm_BookProof_ChapterA3n_projSym_spinGenDiag_comm
-- name    : BookProof.ChapterA3n.projSym_spinGenDiag_comm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:08:58.552679+00:00
-- url     : https://prove2.me/theorems/1408b5b2-3a1f-4701-a737-626a4c4b522c
-- title:
--   `BookProof.ChapterA3n.projSym_spinGenDiag_comm` {N : ℕ} (μ ν : Fin 4) : projSym N * diagGen (spinGen μ ν) = diagGen (spinGen μ ν) * projSym N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3n`.
--
--   `BookProof.ChapterA3n.projSym_spinGenDiag_comm` {N : ℕ} (μ ν : Fin 4) : projSym N * diagGen (spinGen μ ν) = diagGen (spinGen μ ν) * projSym N
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3n.projSym_spinGenDiag_comm`.

-- Generated from ChapterA3n.lean — theorem BookProof.ChapterA3n.projSym_spinGenDiag_comm
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3l
open BookProof.ChapterA3j
open BookProof.ChapterA3l
open BookProof.ChapterA3n


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j

theorem BookProof.ChapterA3n.projSym_spinGenDiag_comm {N : ℕ} (μ ν : Fin 4) :
    projSym N * diagGen (spinGen μ ν) = diagGen (spinGen μ ν) * projSym N := by sorry
