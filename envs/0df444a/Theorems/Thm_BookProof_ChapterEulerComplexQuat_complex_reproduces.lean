-- Prove2me | Theorems.Thm_BookProof_ChapterEulerComplexQuat_complex_reproduces
-- name    : BookProof.ChapterEulerComplexQuat.complex_reproduces
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T02:50:27.156968+00:00
-- url     : https://prove2.me/theorems/e380457f-1533-4591-86d5-31c54b1fb32a
-- title:
--   `BookProof.ChapterEulerComplexQuat.complex_reproduces` (p : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1) : ∃ v : Fin n → ℂ, (∑ k, Complex.normSq (v k) = 1) ∧ ∀ k,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerComplexQuat`.
--
--   `BookProof.ChapterEulerComplexQuat.complex_reproduces` (p : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1) : ∃ v : Fin n → ℂ, (∑ k, Complex.normSq (v k) = 1) ∧ ∀ k, cbornProb v k = p k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerComplexQuat.complex_reproduces`.

-- Generated from ChapterEulerComplexQuat.lean — theorem BookProof.ChapterEulerComplexQuat.complex_reproduces
import Mathlib
import Definitions.Def_ChapterEulerComplexQuat
open BookProof.ChapterEulerComplexQuat


open scoped Quaternion BigOperators


variable {n : ℕ}

theorem BookProof.ChapterEulerComplexQuat.complex_reproduces (p : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∑ k, p k = 1) :
    ∃ v : Fin n → ℂ, (∑ k, Complex.normSq (v k) = 1) ∧ ∀ k, cbornProb v k = p k := by sorry
