-- Prove2me | Theorems.Thm_BookProof_ChapterA3q_projMixed_diagGen_comm
-- name    : BookProof.ChapterA3q.projMixed_diagGen_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T00:36:31.116924+00:00
-- url     : https://prove2.me/theorems/c1782445-0ed2-4779-868a-b84d02bf37b5
-- title:
--   `BookProof.ChapterA3q.projMixed_diagGen_comm` {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) : projMixed N * diagGen A = diagGen A * projMixed N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3q`.
--
--   `BookProof.ChapterA3q.projMixed_diagGen_comm` {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) : projMixed N * diagGen A = diagGen A * projMixed N
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3q.projMixed_diagGen_comm`.

-- Generated from ChapterA3q.lean — theorem BookProof.ChapterA3q.projMixed_diagGen_comm
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3p
import Mathlib
import Definitions.Def_ChapterA3q
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
open BookProof.ChapterA3l
open BookProof.ChapterA3n
open BookProof.ChapterA3o
open BookProof.ChapterA3q


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open BookProof.ChapterA3p

theorem BookProof.ChapterA3q.projMixed_diagGen_comm {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) :
    projMixed N * diagGen A = diagGen A * projMixed N := by sorry
