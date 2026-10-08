-- Prove2me | Theorems.Thm_BookProof_ChapterA3x_projMixed_spinGenDiag_comm
-- name    : BookProof.ChapterA3x.projMixed_spinGenDiag_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:39:27.030007+00:00
-- url     : https://prove2.me/theorems/0ff4ef95-8460-4386-a7b1-3a3a56b39508
-- title:
--   `BookProof.ChapterA3x.projMixed_spinGenDiag_comm` {N : ℕ} (μ ν : Fin 4) : projMixed N * diagGen (spinGen μ ν) = diagGen (spinGen μ ν) * projMixed N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3x`.
--
--   `BookProof.ChapterA3x.projMixed_spinGenDiag_comm` {N : ℕ} (μ ν : Fin 4) : projMixed N * diagGen (spinGen μ ν) = diagGen (spinGen μ ν) * projMixed N
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3x.projMixed_spinGenDiag_comm`.

-- Generated from ChapterA3x.lean — theorem BookProof.ChapterA3x.projMixed_spinGenDiag_comm
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3o
import Definitions.Def_ChapterA3p
import Mathlib
import Definitions.Def_ChapterA3x
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3j
open BookProof.ChapterA3n
open BookProof.ChapterA3x


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open BookProof.ChapterA3p

theorem BookProof.ChapterA3x.projMixed_spinGenDiag_comm {N : ℕ} (μ ν : Fin 4) :
    projMixed N * diagGen (spinGen μ ν) = diagGen (spinGen μ ν) * projMixed N := by sorry
