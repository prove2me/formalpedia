-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaFourier_boost_two_mul
-- name    : BookProof.ChapterMajoranaFourier.boost_two_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:54:55.730089+00:00
-- url     : https://prove2.me/theorems/1d8b6232-9fc4-495c-81ff-9f560f95bedb
-- title:
--   `BookProof.ChapterMajoranaFourier.boost_two_mul` (m q : ℝ) (hm : 0 ≤ m) (hq : 0 < q) : 2 * boostC m q * boostS m q = q / Ep m q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMajoranaFourier`.
--
--   `BookProof.ChapterMajoranaFourier.boost_two_mul` (m q : ℝ) (hm : 0 ≤ m) (hq : 0 < q) : 2 * boostC m q * boostS m q = q / Ep m q
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMajoranaFourier.boost_two_mul`.

-- Generated from ChapterMajoranaFourier.lean — theorem BookProof.ChapterMajoranaFourier.boost_two_mul
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterMajoranaFourier
open BookProof.ChapterMajoranaFourier


open Matrix


open BookProof.ChapterA3

theorem BookProof.ChapterMajoranaFourier.boost_two_mul (m q : ℝ) (hm : 0 ≤ m) (hq : 0 < q) :
    2 * boostC m q * boostS m q = q / Ep m q := by sorry
