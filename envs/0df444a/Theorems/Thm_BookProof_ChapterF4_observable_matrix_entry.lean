-- Prove2me | Theorems.Thm_BookProof_ChapterF4_observable_matrix_entry
-- name    : BookProof.ChapterF4.observable_matrix_entry
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:50:52.42615+00:00
-- url     : https://prove2.me/theorems/8a3bffa0-4ae3-41bc-aa85-33852250ad4c
-- title:
--   `BookProof.ChapterF4.observable_matrix_entry` {d n : ℕ} (W : Matrix (Fin d) (Fin n) ℂ) (a : Fin d) (r s : Fin n) : Matrix.trace ((Matrix.single r s (1 : ℂ))ᴴ * Wᴴ * Matrix.single a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF4`.
--
--   `BookProof.ChapterF4.observable_matrix_entry` {d n : ℕ} (W : Matrix (Fin d) (Fin n) ℂ) (a : Fin d) (r s : Fin n) : Matrix.trace ((Matrix.single r s (1 : ℂ))ᴴ * Wᴴ * Matrix.single a a (1 : ℂ) * W) = (starRingEnd ℂ) (W a r) * W a s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF4.observable_matrix_entry`.

-- Generated from ChapterF4.lean — theorem BookProof.ChapterF4.observable_matrix_entry
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4


open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]
variable {α κ Ω : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  {mΩ : MeasurableSpace Ω}

theorem BookProof.ChapterF4.observable_matrix_entry {d n : ℕ} (W : Matrix (Fin d) (Fin n) ℂ)
    (a : Fin d) (r s : Fin n) :
    Matrix.trace ((Matrix.single r s (1 : ℂ))ᴴ * Wᴴ * Matrix.single a a (1 : ℂ) * W)
      = (starRingEnd ℂ) (W a r) * W a s := by sorry
