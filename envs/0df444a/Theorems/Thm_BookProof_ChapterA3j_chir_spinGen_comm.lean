-- Prove2me | Theorems.Thm_BookProof_ChapterA3j_chir_spinGen_comm
-- name    : BookProof.ChapterA3j.chir_spinGen_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T13:09:34.223976+00:00
-- url     : https://prove2.me/theorems/253729bd-e546-442d-aea4-0573d6031f4a
-- title:
--   `BookProof.ChapterA3j.chir_spinGen_comm` (μ ν : Fin 4) : chir * spinGen μ ν = spinGen μ ν * chir
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3j`.
--
--   `BookProof.ChapterA3j.chir_spinGen_comm` (μ ν : Fin 4) : chir * spinGen μ ν = spinGen μ ν * chir
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3j.chir_spinGen_comm`.

-- Generated from ChapterA3j.lean — theorem BookProof.ChapterA3j.chir_spinGen_comm
import Mathlib
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterA3j


open Matrix


open BookProof.ChapterA3

theorem BookProof.ChapterA3j.chir_spinGen_comm (μ ν : Fin 4) :
    chir * spinGen μ ν = spinGen μ ν * chir := by sorry
