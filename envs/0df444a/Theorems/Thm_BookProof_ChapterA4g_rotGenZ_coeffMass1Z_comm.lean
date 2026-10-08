-- Prove2me | Theorems.Thm_BookProof_ChapterA4g_rotGenZ_coeffMass1Z_comm
-- name    : BookProof.ChapterA4g.rotGenZ_coeffMass1Z_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:48:04.949802+00:00
-- url     : https://prove2.me/theorems/61ef8efe-5fa4-4178-9dfa-5142bd1b405d
-- title:
--   `BookProof.ChapterA4g.rotGenZ_coeffMass1Z_comm` (i j : Fin 3) : rotGenZ i j * coeffMass1Z = coeffMass1Z * rotGenZ i j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4g`.
--
--   `BookProof.ChapterA4g.rotGenZ_coeffMass1Z_comm` (i j : Fin 3) : rotGenZ i j * coeffMass1Z = coeffMass1Z * rotGenZ i j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4g.rotGenZ_coeffMass1Z_comm`.

-- Generated from ChapterA4g.lean — theorem BookProof.ChapterA4g.rotGenZ_coeffMass1Z_comm
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4g
import Definitions.Def_ChapterA5
open BookProof.ChapterA5
open BookProof.ChapterA4g


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

theorem BookProof.ChapterA4g.rotGenZ_coeffMass1Z_comm (i j : Fin 3) :
    rotGenZ i j * coeffMass1Z = coeffMass1Z * rotGenZ i j := by sorry
