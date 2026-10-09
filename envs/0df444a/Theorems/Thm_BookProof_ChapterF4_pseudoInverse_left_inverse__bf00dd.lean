-- Prove2me | Theorems.Thm_BookProof_ChapterF4_pseudoInverse_left_inverse__bf00dd
-- name    : BookProof.ChapterF4.pseudoInverse_left_inverse
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:50:57.017974+00:00
-- url     : https://prove2.me/theorems/bf00dd35-c272-488a-948a-183f34b7c023
-- title:
--   `BookProof.ChapterF4.pseudoInverse_left_inverse` {k m : ℕ} (Φ : Matrix (Fin k) (Fin m) ℝ) [Invertible (Φᵀ * Φ)] : ⅟(Φᵀ * Φ) * Φᵀ * Φ = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF4`.
--
--   `BookProof.ChapterF4.pseudoInverse_left_inverse` {k m : ℕ} (Φ : Matrix (Fin k) (Fin m) ℝ) [Invertible (Φᵀ * Φ)] : ⅟(Φᵀ * Φ) * Φᵀ * Φ = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF4.pseudoInverse_left_inverse`.

-- Generated from ChapterF4.lean — theorem BookProof.ChapterF4.pseudoInverse_left_inverse
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4


open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]
variable {α κ Ω : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  {mΩ : MeasurableSpace Ω}

theorem BookProof.ChapterF4.pseudoInverse_left_inverse {k m : ℕ} (Φ : Matrix (Fin k) (Fin m) ℝ)
    [Invertible (Φᵀ * Φ)] :
    ⅟(Φᵀ * Φ) * Φᵀ * Φ = 1 := by sorry
