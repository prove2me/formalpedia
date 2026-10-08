-- Prove2me | Theorems.Thm_BookProof_ChapterA4g_rotGen_projPos_comm
-- name    : BookProof.ChapterA4g.rotGen_projPos_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:48:14.524009+00:00
-- url     : https://prove2.me/theorems/0bdd395e-835a-4c96-9591-f68cbe0560a6
-- title:
--   `BookProof.ChapterA4g.rotGen_projPos_comm` (i j : Fin 3) : rotGen i j * projPos = projPos * rotGen i j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4g`.
--
--   `BookProof.ChapterA4g.rotGen_projPos_comm` (i j : Fin 3) : rotGen i j * projPos = projPos * rotGen i j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4g.rotGen_projPos_comm`.

-- Generated from ChapterA4g.lean — theorem BookProof.ChapterA4g.rotGen_projPos_comm
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4g
import Definitions.Def_ChapterA4e
open BookProof.ChapterA4e
open BookProof.ChapterA4g


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

theorem BookProof.ChapterA4g.rotGen_projPos_comm (i j : Fin 3) :
    rotGen i j * projPos = projPos * rotGen i j := by sorry
