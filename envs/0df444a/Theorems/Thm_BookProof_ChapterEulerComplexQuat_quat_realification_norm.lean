-- Prove2me | Theorems.Thm_BookProof_ChapterEulerComplexQuat_quat_realification_norm
-- name    : BookProof.ChapterEulerComplexQuat.quat_realification_norm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T02:51:16.54461+00:00
-- url     : https://prove2.me/theorems/3f004d4e-1bd5-450e-93b0-ab477ebf8795
-- title:
--   `BookProof.ChapterEulerComplexQuat.quat_realification_norm` (v : Fin n → ℍ[ℝ]) : ∑ k, ((v k).re ^ 2 + (v k).imI ^ 2 + (v k).imJ ^ 2 + (v k).imK ^ 2) = ∑ k, qbornProb v k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerComplexQuat`.
--
--   `BookProof.ChapterEulerComplexQuat.quat_realification_norm` (v : Fin n → ℍ[ℝ]) : ∑ k, ((v k).re ^ 2 + (v k).imI ^ 2 + (v k).imJ ^ 2 + (v k).imK ^ 2) = ∑ k, qbornProb v k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerComplexQuat.quat_realification_norm`.

-- Generated from ChapterEulerComplexQuat.lean — theorem BookProof.ChapterEulerComplexQuat.quat_realification_norm
import Mathlib
import Definitions.Def_ChapterEulerComplexQuat
open BookProof.ChapterEulerComplexQuat


open scoped Quaternion BigOperators


variable {n : ℕ}

theorem BookProof.ChapterEulerComplexQuat.quat_realification_norm (v : Fin n → ℍ[ℝ]) :
    ∑ k, ((v k).re ^ 2 + (v k).imI ^ 2 + (v k).imJ ^ 2 + (v k).imK ^ 2)
      = ∑ k, qbornProb v k := by sorry
