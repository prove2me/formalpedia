-- Prove2me | Theorems.Thm_BookProof_ChapterA3j_projChirL_spinGen_comm
-- name    : BookProof.ChapterA3j.projChirL_spinGen_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T13:12:47.301319+00:00
-- url     : https://prove2.me/theorems/e060edc6-26aa-4c7c-b7d3-76c927632853
-- title:
--   `BookProof.ChapterA3j.projChirL_spinGen_comm` (μ ν : Fin 4) : projChirL * spinGen μ ν = spinGen μ ν * projChirL
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3j`.
--
--   `BookProof.ChapterA3j.projChirL_spinGen_comm` (μ ν : Fin 4) : projChirL * spinGen μ ν = spinGen μ ν * projChirL
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3j.projChirL_spinGen_comm`.

-- Generated from ChapterA3j.lean — theorem BookProof.ChapterA3j.projChirL_spinGen_comm
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA3j
open BookProof.ChapterA3j


open Matrix


open BookProof.ChapterA3

theorem BookProof.ChapterA3j.projChirL_spinGen_comm (μ ν : Fin 4) :
    projChirL * spinGen μ ν = spinGen μ ν * projChirL := by sorry
