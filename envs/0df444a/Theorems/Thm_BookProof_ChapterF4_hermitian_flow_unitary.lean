-- Prove2me | Theorems.Thm_BookProof_ChapterF4_hermitian_flow_unitary
-- name    : BookProof.ChapterF4.hermitian_flow_unitary
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:51:09.261979+00:00
-- url     : https://prove2.me/theorems/761ee82e-c417-4f52-a6d6-8c6be1427a14
-- title:
--   `BookProof.ChapterF4.hermitian_flow_unitary` {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) : (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H))ᴴ * NormedSpace.exp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF4`.
--
--   `BookProof.ChapterF4.hermitian_flow_unitary` {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) : (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H))ᴴ * NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF4.hermitian_flow_unitary`.

-- Generated from ChapterF4.lean — theorem BookProof.ChapterF4.hermitian_flow_unitary
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4


open scoped BigOperators Matrix

variable {d k : ℕ}
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]
variable {α κ Ω : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
  {mΩ : MeasurableSpace Ω}

theorem BookProof.ChapterF4.hermitian_flow_unitary {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (t : ℝ) :
    (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H))ᴴ
        * NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) = 1 := by sorry
