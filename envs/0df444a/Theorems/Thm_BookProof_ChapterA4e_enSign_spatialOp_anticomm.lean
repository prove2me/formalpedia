-- Prove2me | Theorems.Thm_BookProof_ChapterA4e_enSign_spatialOp_anticomm
-- name    : BookProof.ChapterA4e.enSign_spatialOp_anticomm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:40:40.596367+00:00
-- url     : https://prove2.me/theorems/6c2da7d6-9dd9-43be-8785-b6ffde2e9798
-- title:
--   `BookProof.ChapterA4e.enSign_spatialOp_anticomm` (j : Fin 3) : enSign * spatialOp j + spatialOp j * enSign = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4e`.
--
--   `BookProof.ChapterA4e.enSign_spatialOp_anticomm` (j : Fin 3) : enSign * spatialOp j + spatialOp j * enSign = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4e.enSign_spatialOp_anticomm`.

-- Generated from ChapterA4e.lean — theorem BookProof.ChapterA4e.enSign_spatialOp_anticomm
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4e
import Definitions.Def_ChapterA5
open BookProof.ChapterA5
open BookProof.ChapterA4e


open Matrix


open BookProof.ChapterA3 BookProof.ChapterA5

theorem BookProof.ChapterA4e.enSign_spatialOp_anticomm (j : Fin 3) :
    enSign * spatialOp j + spatialOp j * enSign = 0 := by sorry
