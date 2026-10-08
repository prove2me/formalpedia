-- Prove2me | Theorems.Thm_BookProof_ChapterA3n_sum_permMat_sq
-- name    : BookProof.ChapterA3n.sum_permMat_sq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:09:17.185031+00:00
-- url     : https://prove2.me/theorems/65c5a112-c88b-47b1-930d-9f96f1a3a400
-- title:
--   `BookProof.ChapterA3n.sum_permMat_sq` {N : ℕ} : (∑ σ : Equiv.Perm (Fin N), permMat σ) * (∑ σ : Equiv.Perm (Fin N), permMat σ) = (Nat.factorial N : ℂ) • ∑ σ : Equiv.Perm (Fin N), pe
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3n`.
--
--   `BookProof.ChapterA3n.sum_permMat_sq` {N : ℕ} : (∑ σ : Equiv.Perm (Fin N), permMat σ) * (∑ σ : Equiv.Perm (Fin N), permMat σ) = (Nat.factorial N : ℂ) • ∑ σ : Equiv.Perm (Fin N), permMat σ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3n.sum_permMat_sq`.

-- Generated from ChapterA3n.lean — theorem BookProof.ChapterA3n.sum_permMat_sq
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Mathlib
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j

theorem BookProof.ChapterA3n.sum_permMat_sq {N : ℕ} :
    (∑ σ : Equiv.Perm (Fin N), permMat σ) * (∑ σ : Equiv.Perm (Fin N), permMat σ)
      = (Nat.factorial N : ℂ) • ∑ σ : Equiv.Perm (Fin N), permMat σ := by sorry
