-- Prove2me | Theorems.Thm_BookProof_ChapterA4g_rotGen_enSign_comm
-- name    : BookProof.ChapterA4g.rotGen_enSign_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:48:18.935644+00:00
-- url     : https://prove2.me/theorems/28a5aaa8-2aa0-43c3-a301-05e28730388d
-- title:
--   `BookProof.ChapterA4g.rotGen_enSign_comm` (i j : Fin 3) : rotGen i j * enSign = enSign * rotGen i j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4g`.
--
--   `BookProof.ChapterA4g.rotGen_enSign_comm` (i j : Fin 3) : rotGen i j * enSign = enSign * rotGen i j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4g.rotGen_enSign_comm`.

-- Generated from ChapterA4g.lean — theorem BookProof.ChapterA4g.rotGen_enSign_comm
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4g
import Definitions.Def_ChapterA4e
import Definitions.Def_ChapterA5
open BookProof.ChapterA4e
open BookProof.ChapterA5
open BookProof.ChapterA4g


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

theorem BookProof.ChapterA4g.rotGen_enSign_comm (i j : Fin 3) :
    rotGen i j * enSign = enSign * rotGen i j := by sorry
