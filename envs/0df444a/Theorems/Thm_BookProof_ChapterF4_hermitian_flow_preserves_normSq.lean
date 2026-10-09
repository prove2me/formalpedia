-- Prove2me | Theorems.Thm_BookProof_ChapterF4_hermitian_flow_preserves_normSq
-- name    : BookProof.ChapterF4.hermitian_flow_preserves_normSq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:52:12.058175+00:00
-- url     : https://prove2.me/theorems/8663f0ad-1a7f-43ad-988b-79b898254d4c
-- title:
--   `BookProof.ChapterF4.hermitian_flow_preserves_normSq` {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) (c : Fin n → ℂ) : star ((NormedSpace.exp ((-Complex.I * (t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF4`.
--
--   `BookProof.ChapterF4.hermitian_flow_preserves_normSq` {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) (c : Fin n → ℂ) : star ((NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)).mulVec c) ⬝ᵥ (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)).mulVec c = star c ⬝ᵥ c
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF4.hermitian_flow_preserves_normSq`.

-- Generated from ChapterF4.lean — theorem BookProof.ChapterF4.hermitian_flow_preserves_normSq
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4


open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]
variable {α κ Ω : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  {mΩ : MeasurableSpace Ω}

theorem BookProof.ChapterF4.hermitian_flow_preserves_normSq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) (c : Fin n → ℂ) :
    star ((NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)).mulVec c)
          ⬝ᵥ (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)).mulVec c
      = star c ⬝ᵥ c := by sorry
