-- Prove2me | Theorems.Thm_BookProof_ChapterF4_pseudoinverse_left_inverse
-- name    : BookProof.ChapterF4.pseudoinverse_left_inverse
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:50:22.785649+00:00
-- url     : https://prove2.me/theorems/6ea5ec4d-75dc-4734-8ff2-e4e12475f6ff
-- title:
--   `BookProof.ChapterF4.pseudoinverse_left_inverse` {m n : ℕ} (Φ : Matrix (Fin m) (Fin n) ℂ) (h : IsUnit (Φᴴ * Φ).det) : ((Φᴴ * Φ)⁻¹ * Φᴴ) * Φ = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF4`.
--
--   `BookProof.ChapterF4.pseudoinverse_left_inverse` {m n : ℕ} (Φ : Matrix (Fin m) (Fin n) ℂ) (h : IsUnit (Φᴴ * Φ).det) : ((Φᴴ * Φ)⁻¹ * Φᴴ) * Φ = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF4.pseudoinverse_left_inverse`.

-- Generated from ChapterF4.lean — theorem BookProof.ChapterF4.pseudoinverse_left_inverse
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4


open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

theorem BookProof.ChapterF4.pseudoinverse_left_inverse {m n : ℕ} (Φ : Matrix (Fin m) (Fin n) ℂ)
    (h : IsUnit (Φᴴ * Φ).det) :
    ((Φᴴ * Φ)⁻¹ * Φᴴ) * Φ = 1 := by sorry
