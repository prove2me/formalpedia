-- Prove2me | Theorems.Thm_BookProof_ChapterA4e_spatialOp_swaps_pos
-- name    : BookProof.ChapterA4e.spatialOp_swaps_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:41:23.667984+00:00
-- url     : https://prove2.me/theorems/460f6c24-86ff-47c2-a28c-15a102f94748
-- title:
--   `BookProof.ChapterA4e.spatialOp_swaps_pos` (j : Fin 3) : projPos * spatialOp j = spatialOp j * projNeg
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4e`.
--
--   `BookProof.ChapterA4e.spatialOp_swaps_pos` (j : Fin 3) : projPos * spatialOp j = spatialOp j * projNeg
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4e.spatialOp_swaps_pos`.

-- Generated from ChapterA4e.lean — theorem BookProof.ChapterA4e.spatialOp_swaps_pos
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4e
open BookProof.ChapterA4e


open Matrix


open BookProof.ChapterA3 BookProof.ChapterA5

theorem BookProof.ChapterA4e.spatialOp_swaps_pos (j : Fin 3) :
    projPos * spatialOp j = spatialOp j * projNeg := by sorry
