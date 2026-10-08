-- Prove2me | Theorems.Thm_BookProof_ChapterF4_observable_matrix_identity
-- name    : BookProof.ChapterF4.observable_matrix_identity
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:49:50.197079+00:00
-- url     : https://prove2.me/theorems/8df65805-1a99-4f37-99db-75a18dac70eb
-- title:
--   `BookProof.ChapterF4.observable_matrix_identity` {dd kk : ℕ} (W : Matrix (Fin dd) (Fin kk) ℂ) (a : Fin dd) (r s : Fin kk) : Matrix.trace ((Matrix.single r s (1 : ℂ) : Matrix (Fin k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF4`.
--
--   `BookProof.ChapterF4.observable_matrix_identity` {dd kk : ℕ} (W : Matrix (Fin dd) (Fin kk) ℂ) (a : Fin dd) (r s : Fin kk) : Matrix.trace ((Matrix.single r s (1 : ℂ) : Matrix (Fin kk) (Fin kk) ℂ)ᴴ * Wᴴ * (Matrix.single a a (1 : ℂ) : Matrix (Fin dd) (Fin dd) ℂ) * W) = (starRingEnd ℂ) (W a r) * W a s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF4.observable_matrix_identity`.

-- Generated from ChapterF4.lean — theorem BookProof.ChapterF4.observable_matrix_identity
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4


open scoped BigOperators Matrix

variable {d k : ℕ}

theorem BookProof.ChapterF4.observable_matrix_identity {dd kk : ℕ} (W : Matrix (Fin dd) (Fin kk) ℂ)
    (a : Fin dd) (r s : Fin kk) :
    Matrix.trace ((Matrix.single r s (1 : ℂ) : Matrix (Fin kk) (Fin kk) ℂ)ᴴ * Wᴴ
        * (Matrix.single a a (1 : ℂ) : Matrix (Fin dd) (Fin dd) ℂ) * W)
      = (starRingEnd ℂ) (W a r) * W a s := by sorry
