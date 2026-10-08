-- Prove2me | Theorems.Thm_BookProof_ChapterA3o_sum_signed_permMat_sq
-- name    : BookProof.ChapterA3o.sum_signed_permMat_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T00:34:06.13633+00:00
-- url     : https://prove2.me/theorems/2f76ed67-6cca-4a4c-ba9e-4fb9f289118b
-- title:
--   `BookProof.ChapterA3o.sum_signed_permMat_sq` {N : ℕ} : (∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ) * (∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ) = (Nat.factorial N :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3o`.
--
--   `BookProof.ChapterA3o.sum_signed_permMat_sq` {N : ℕ} : (∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ) * (∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ) = (Nat.factorial N : ℂ) • ∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3o.sum_signed_permMat_sq`.

-- Generated from ChapterA3o.lean — theorem BookProof.ChapterA3o.sum_signed_permMat_sq
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

theorem BookProof.ChapterA3o.sum_signed_permMat_sq {N : ℕ} :
    (∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ) *
        (∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ)
      = (Nat.factorial N : ℂ) • ∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ := by sorry
