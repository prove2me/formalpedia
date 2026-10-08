-- Prove2me | Theorems.Thm_BookProof_ChapterA4e_spatialOp_swaps_neg
-- name    : BookProof.ChapterA4e.spatialOp_swaps_neg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:41:35.992747+00:00
-- url     : https://prove2.me/theorems/fbcb6c6e-3dc5-4426-a108-7d4c3901e31a
-- title:
--   `BookProof.ChapterA4e.spatialOp_swaps_neg` (j : Fin 3) : projNeg * spatialOp j = spatialOp j * projPos
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4e`.
--
--   `BookProof.ChapterA4e.spatialOp_swaps_neg` (j : Fin 3) : projNeg * spatialOp j = spatialOp j * projPos
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4e.spatialOp_swaps_neg`.

-- Generated from ChapterA4e.lean — theorem BookProof.ChapterA4e.spatialOp_swaps_neg
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4e
open BookProof.ChapterA4e


open Matrix


open BookProof.ChapterA3 BookProof.ChapterA5

theorem BookProof.ChapterA4e.spatialOp_swaps_neg (j : Fin 3) :
    projNeg * spatialOp j = spatialOp j * projPos := by sorry
