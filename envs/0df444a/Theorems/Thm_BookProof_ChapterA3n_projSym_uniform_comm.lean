-- Prove2me | Theorems.Thm_BookProof_ChapterA3n_projSym_uniform_comm
-- name    : BookProof.ChapterA3n.projSym_uniform_comm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:08:32.421976+00:00
-- url     : https://prove2.me/theorems/369e395e-8c7f-441b-a03e-174ff23ac2e6
-- title:
--   `BookProof.ChapterA3n.projSym_uniform_comm` {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) : projSym N * uniform A = uniform A * projSym N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3n`.
--
--   `BookProof.ChapterA3n.projSym_uniform_comm` {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) : projSym N * uniform A = uniform A * projSym N
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3n.projSym_uniform_comm`.

-- Generated from ChapterA3n.lean — theorem BookProof.ChapterA3n.projSym_uniform_comm
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

theorem BookProof.ChapterA3n.projSym_uniform_comm {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) :
    projSym N * uniform A = uniform A * projSym N := by sorry
