-- Prove2me | Theorems.Thm_BookProof_ChapterEulerComplexQuat_quat_reproduces
-- name    : BookProof.ChapterEulerComplexQuat.quat_reproduces
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T02:51:43.976218+00:00
-- url     : https://prove2.me/theorems/c279b7d9-bd0e-4ee4-9502-1ef571c41b8b
-- title:
--   `BookProof.ChapterEulerComplexQuat.quat_reproduces` (p : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1) : ∃ v : Fin n → ℍ[ℝ], (∑ k, Quaternion.normSq (v k) = 1) ∧ ∀...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerComplexQuat`.
--
--   `BookProof.ChapterEulerComplexQuat.quat_reproduces` (p : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1) : ∃ v : Fin n → ℍ[ℝ], (∑ k, Quaternion.normSq (v k) = 1) ∧ ∀ k, qbornProb v k = p k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerComplexQuat.quat_reproduces`.

-- Generated from ChapterEulerComplexQuat.lean — theorem BookProof.ChapterEulerComplexQuat.quat_reproduces
import Mathlib
import Definitions.Def_ChapterEulerComplexQuat
open BookProof.ChapterEulerComplexQuat


open scoped Quaternion BigOperators


variable {n : ℕ}

theorem BookProof.ChapterEulerComplexQuat.quat_reproduces (p : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∑ k, p k = 1) :
    ∃ v : Fin n → ℍ[ℝ], (∑ k, Quaternion.normSq (v k) = 1) ∧ ∀ k, qbornProb v k = p k := by sorry
