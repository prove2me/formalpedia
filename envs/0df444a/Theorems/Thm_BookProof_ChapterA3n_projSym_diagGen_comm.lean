-- Prove2me | Theorems.Thm_BookProof_ChapterA3n_projSym_diagGen_comm
-- name    : BookProof.ChapterA3n.projSym_diagGen_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:08:44.707509+00:00
-- url     : https://prove2.me/theorems/3da36b21-fbde-4c80-b32e-72a8eaa92715
-- title:
--   `BookProof.ChapterA3n.projSym_diagGen_comm` {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) : projSym N * diagGen A = diagGen A * projSym N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3n`.
--
--   `BookProof.ChapterA3n.projSym_diagGen_comm` {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) : projSym N * diagGen A = diagGen A * projSym N
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3n.projSym_diagGen_comm`.

-- Generated from ChapterA3n.lean — theorem BookProof.ChapterA3n.projSym_diagGen_comm
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Mathlib
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3l
open BookProof.ChapterA3l
open BookProof.ChapterA3n


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j

theorem BookProof.ChapterA3n.projSym_diagGen_comm {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) :
    projSym N * diagGen A = diagGen A * projSym N := by sorry
