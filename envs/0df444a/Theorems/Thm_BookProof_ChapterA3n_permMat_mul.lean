-- Prove2me | Theorems.Thm_BookProof_ChapterA3n_permMat_mul
-- name    : BookProof.ChapterA3n.permMat_mul
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:07:20.838056+00:00
-- url     : https://prove2.me/theorems/b4ec9c3d-b481-45b0-bacc-2665c92443a3
-- title:
--   `BookProof.ChapterA3n.permMat_mul` {N : ℕ} (σ τ : Equiv.Perm (Fin N)) : permMat σ * permMat τ = permMat (σ * τ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3n`.
--
--   `BookProof.ChapterA3n.permMat_mul` {N : ℕ} (σ τ : Equiv.Perm (Fin N)) : permMat σ * permMat τ = permMat (σ * τ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3n.permMat_mul`.

-- Generated from ChapterA3n.lean — theorem BookProof.ChapterA3n.permMat_mul
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Mathlib
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j

theorem BookProof.ChapterA3n.permMat_mul {N : ℕ} (σ τ : Equiv.Perm (Fin N)) :
    permMat σ * permMat τ = permMat (σ * τ) := by sorry
