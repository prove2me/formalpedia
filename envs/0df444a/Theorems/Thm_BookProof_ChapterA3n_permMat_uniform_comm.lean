-- Prove2me | Theorems.Thm_BookProof_ChapterA3n_permMat_uniform_comm
-- name    : BookProof.ChapterA3n.permMat_uniform_comm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:07:59.068054+00:00
-- url     : https://prove2.me/theorems/eda80b72-d6b6-416e-af4a-05958a52ff8c
-- title:
--   `BookProof.ChapterA3n.permMat_uniform_comm` {N : ℕ} (σ : Equiv.Perm (Fin N)) (A : Matrix (Fin 4) (Fin 4) ℂ) : permMat σ * uniform A = uniform A * permMat σ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3n`.
--
--   `BookProof.ChapterA3n.permMat_uniform_comm` {N : ℕ} (σ : Equiv.Perm (Fin N)) (A : Matrix (Fin 4) (Fin 4) ℂ) : permMat σ * uniform A = uniform A * permMat σ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3n.permMat_uniform_comm`.

-- Generated from ChapterA3n.lean — theorem BookProof.ChapterA3n.permMat_uniform_comm
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Mathlib
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j

theorem BookProof.ChapterA3n.permMat_uniform_comm {N : ℕ} (σ : Equiv.Perm (Fin N))
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    permMat σ * uniform A = uniform A * permMat σ := by sorry
