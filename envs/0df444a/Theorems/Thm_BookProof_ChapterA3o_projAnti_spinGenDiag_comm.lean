-- Prove2me | Theorems.Thm_BookProof_ChapterA3o_projAnti_spinGenDiag_comm
-- name    : BookProof.ChapterA3o.projAnti_spinGenDiag_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T00:34:47.188277+00:00
-- url     : https://prove2.me/theorems/011688e0-d186-4eeb-ad88-41c6c54bd75e
-- title:
--   `BookProof.ChapterA3o.projAnti_spinGenDiag_comm` {N : ℕ} (μ ν : Fin 4) : projAnti N * diagGen (spinGen μ ν) = diagGen (spinGen μ ν) * projAnti N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3o`.
--
--   `BookProof.ChapterA3o.projAnti_spinGenDiag_comm` {N : ℕ} (μ ν : Fin 4) : projAnti N * diagGen (spinGen μ ν) = diagGen (spinGen μ ν) * projAnti N
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3o.projAnti_spinGenDiag_comm`.

-- Generated from ChapterA3o.lean — theorem BookProof.ChapterA3o.projAnti_spinGenDiag_comm
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA3o
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3j
open BookProof.ChapterA3n
open BookProof.ChapterA3o


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n

theorem BookProof.ChapterA3o.projAnti_spinGenDiag_comm {N : ℕ} (μ ν : Fin 4) :
    projAnti N * diagGen (spinGen μ ν) = diagGen (spinGen μ ν) * projAnti N := by sorry
