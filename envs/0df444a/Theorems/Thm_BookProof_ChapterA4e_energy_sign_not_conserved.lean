-- Prove2me | Theorems.Thm_BookProof_ChapterA4e_energy_sign_not_conserved
-- name    : BookProof.ChapterA4e.energy_sign_not_conserved
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:41:55.566503+00:00
-- url     : https://prove2.me/theorems/cd4c13f8-b780-4b66-904f-860235d74137
-- title:
--   `BookProof.ChapterA4e.energy_sign_not_conserved` : ∃ j : Fin 3, projPos * spatialOp j ≠ spatialOp j * projPos
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4e`.
--
--   `BookProof.ChapterA4e.energy_sign_not_conserved` : ∃ j : Fin 3, projPos * spatialOp j ≠ spatialOp j * projPos
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4e.energy_sign_not_conserved`.

-- Generated from ChapterA4e.lean — theorem BookProof.ChapterA4e.energy_sign_not_conserved
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4e
import Definitions.Def_ChapterA5
open BookProof.ChapterA5
open BookProof.ChapterA4e


open Matrix


open BookProof.ChapterA3 BookProof.ChapterA5

theorem BookProof.ChapterA4e.energy_sign_not_conserved :
    ∃ j : Fin 3, projPos * spatialOp j ≠ spatialOp j * projPos := by sorry
