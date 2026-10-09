-- Prove2me | Theorems.Thm_BookProof_ChapterEulerComplexQuat_quat_born_split
-- name    : BookProof.ChapterEulerComplexQuat.quat_born_split
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T02:51:04.933079+00:00
-- url     : https://prove2.me/theorems/b4bfdaa5-ccbb-4a99-a9a7-255afe0ca615
-- title:
--   `BookProof.ChapterEulerComplexQuat.quat_born_split` (v : Fin n → ℍ[ℝ]) (k : Fin n) : qbornProb v k = (v k).re ^ 2 + (v k).imI ^ 2 + (v k).imJ ^ 2 + (v k).imK ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerComplexQuat`.
--
--   `BookProof.ChapterEulerComplexQuat.quat_born_split` (v : Fin n → ℍ[ℝ]) (k : Fin n) : qbornProb v k = (v k).re ^ 2 + (v k).imI ^ 2 + (v k).imJ ^ 2 + (v k).imK ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerComplexQuat.quat_born_split`.

-- Generated from ChapterEulerComplexQuat.lean — theorem BookProof.ChapterEulerComplexQuat.quat_born_split
import Mathlib
import Definitions.Def_ChapterEulerComplexQuat
open BookProof.ChapterEulerComplexQuat


open scoped Quaternion BigOperators


variable {n : ℕ}

theorem BookProof.ChapterEulerComplexQuat.quat_born_split (v : Fin n → ℍ[ℝ]) (k : Fin n) :
    qbornProb v k =
      (v k).re ^ 2 + (v k).imI ^ 2 + (v k).imJ ^ 2 + (v k).imK ^ 2 := by sorry
