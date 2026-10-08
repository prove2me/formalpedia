-- Prove2me | Theorems.Thm_BookProof_ChapterA3o_projAnti_uniform_comm
-- name    : BookProof.ChapterA3o.projAnti_uniform_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T00:34:22.091501+00:00
-- url     : https://prove2.me/theorems/17759f17-c096-4e38-8f54-f97d5f313bf8
-- title:
--   `BookProof.ChapterA3o.projAnti_uniform_comm` {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) : projAnti N * uniform A = uniform A * projAnti N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3o`.
--
--   `BookProof.ChapterA3o.projAnti_uniform_comm` {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) : projAnti N * uniform A = uniform A * projAnti N
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3o.projAnti_uniform_comm`.

-- Generated from ChapterA3o.lean — theorem BookProof.ChapterA3o.projAnti_uniform_comm
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Mathlib
import Definitions.Def_ChapterA3o
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n
open BookProof.ChapterA3o


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n

theorem BookProof.ChapterA3o.projAnti_uniform_comm {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) :
    projAnti N * uniform A = uniform A * projAnti N := by sorry
