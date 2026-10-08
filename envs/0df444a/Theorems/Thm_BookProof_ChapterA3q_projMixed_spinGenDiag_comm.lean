-- Prove2me | Theorems.Thm_BookProof_ChapterA3q_projMixed_spinGenDiag_comm
-- name    : BookProof.ChapterA3q.projMixed_spinGenDiag_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T00:36:49.42222+00:00
-- url     : https://prove2.me/theorems/4b1fff1b-699c-4956-84e0-932ca13bb3f1
-- title:
--   `BookProof.ChapterA3q.projMixed_spinGenDiag_comm` {N : ℕ} (μ ν : Fin 4) : projMixed N * diagGen (spinGen μ ν) = diagGen (spinGen μ ν) * projMixed N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3q`.
--
--   `BookProof.ChapterA3q.projMixed_spinGenDiag_comm` {N : ℕ} (μ ν : Fin 4) : projMixed N * diagGen (spinGen μ ν) = diagGen (spinGen μ ν) * projMixed N
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3q.projMixed_spinGenDiag_comm`.

-- Generated from ChapterA3q.lean — theorem BookProof.ChapterA3q.projMixed_spinGenDiag_comm
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3o
import Definitions.Def_ChapterA3p
import Mathlib
import Definitions.Def_ChapterA3q
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3j
open BookProof.ChapterA3n
open BookProof.ChapterA3q


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open BookProof.ChapterA3p

theorem BookProof.ChapterA3q.projMixed_spinGenDiag_comm {N : ℕ} (μ ν : Fin 4) :
    projMixed N * diagGen (spinGen μ ν) = diagGen (spinGen μ ν) * projMixed N := by sorry
