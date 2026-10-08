-- Prove2me | Theorems.Thm_BookProof_ChapterEulerComplexQuat_complex_born_split
-- name    : BookProof.ChapterEulerComplexQuat.complex_born_split
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T02:49:55.216568+00:00
-- url     : https://prove2.me/theorems/799b3fc1-fb2c-45c7-b460-0eeff933687f
-- title:
--   `BookProof.ChapterEulerComplexQuat.complex_born_split` (v : Fin n → ℂ) (k : Fin n) : cbornProb v k = (v k).re ^ 2 + (v k).im ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerComplexQuat`.
--
--   `BookProof.ChapterEulerComplexQuat.complex_born_split` (v : Fin n → ℂ) (k : Fin n) : cbornProb v k = (v k).re ^ 2 + (v k).im ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerComplexQuat.complex_born_split`.

-- Generated from ChapterEulerComplexQuat.lean — theorem BookProof.ChapterEulerComplexQuat.complex_born_split
import Mathlib
import Definitions.Def_ChapterEulerComplexQuat
open BookProof.ChapterEulerComplexQuat


open scoped Quaternion BigOperators


variable {n : ℕ}

theorem BookProof.ChapterEulerComplexQuat.complex_born_split (v : Fin n → ℂ) (k : Fin n) :
    cbornProb v k = (v k).re ^ 2 + (v k).im ^ 2 := by sorry
