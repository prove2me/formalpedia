-- Prove2me | Theorems.Thm_BookProof_ChapterA3j_projChirR_spinGen_comm
-- name    : BookProof.ChapterA3j.projChirR_spinGen_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T13:30:02.057232+00:00
-- url     : https://prove2.me/theorems/9c721853-b281-4120-8962-b7e5312344a5
-- title:
--   `BookProof.ChapterA3j.projChirR_spinGen_comm` (μ ν : Fin 4) : projChirR * spinGen μ ν = spinGen μ ν * projChirR
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3j`.
--
--   `BookProof.ChapterA3j.projChirR_spinGen_comm` (μ ν : Fin 4) : projChirR * spinGen μ ν = spinGen μ ν * projChirR
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3j.projChirR_spinGen_comm`.

-- Generated from ChapterA3j.lean — theorem BookProof.ChapterA3j.projChirR_spinGen_comm
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA3j
open BookProof.ChapterA3j


open Matrix


open BookProof.ChapterA3

theorem BookProof.ChapterA3j.projChirR_spinGen_comm (μ ν : Fin 4) :
    projChirR * spinGen μ ν = spinGen μ ν * projChirR := by sorry
