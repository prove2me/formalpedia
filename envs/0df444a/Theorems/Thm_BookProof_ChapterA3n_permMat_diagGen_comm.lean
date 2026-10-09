-- Prove2me | Theorems.Thm_BookProof_ChapterA3n_permMat_diagGen_comm
-- name    : BookProof.ChapterA3n.permMat_diagGen_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:07:57.853112+00:00
-- url     : https://prove2.me/theorems/35d8aaf0-9a3e-4a0d-bef3-77f26e34188e
-- title:
--   `BookProof.ChapterA3n.permMat_diagGen_comm` {N : ℕ} (σ : Equiv.Perm (Fin N)) (A : Matrix (Fin 4) (Fin 4) ℂ) : permMat σ * diagGen A = diagGen A * permMat σ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3n`.
--
--   `BookProof.ChapterA3n.permMat_diagGen_comm` {N : ℕ} (σ : Equiv.Perm (Fin N)) (A : Matrix (Fin 4) (Fin 4) ℂ) : permMat σ * diagGen A = diagGen A * permMat σ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3n.permMat_diagGen_comm`.

-- Generated from ChapterA3n.lean — theorem BookProof.ChapterA3n.permMat_diagGen_comm
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Mathlib
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j

theorem BookProof.ChapterA3n.permMat_diagGen_comm {N : ℕ} (σ : Equiv.Perm (Fin N))
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    permMat σ * diagGen A = diagGen A * permMat σ := by sorry
