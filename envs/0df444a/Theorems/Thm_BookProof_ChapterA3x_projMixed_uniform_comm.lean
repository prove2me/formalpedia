-- Prove2me | Theorems.Thm_BookProof_ChapterA3x_projMixed_uniform_comm
-- name    : BookProof.ChapterA3x.projMixed_uniform_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:39:15.798375+00:00
-- url     : https://prove2.me/theorems/4d8000aa-eb49-4498-908d-df11daf0e28f
-- title:
--   `BookProof.ChapterA3x.projMixed_uniform_comm` {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) : projMixed N * uniform A = uniform A * projMixed N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3x`.
--
--   `BookProof.ChapterA3x.projMixed_uniform_comm` {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) : projMixed N * uniform A = uniform A * projMixed N
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3x.projMixed_uniform_comm`.

-- Generated from ChapterA3x.lean — theorem BookProof.ChapterA3x.projMixed_uniform_comm
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3p
import Mathlib
import Definitions.Def_ChapterA3x
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
open BookProof.ChapterA3l
open BookProof.ChapterA3n
open BookProof.ChapterA3o
open BookProof.ChapterA3x


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open BookProof.ChapterA3p

theorem BookProof.ChapterA3x.projMixed_uniform_comm {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) :
    projMixed N * uniform A = uniform A * projMixed N := by sorry
