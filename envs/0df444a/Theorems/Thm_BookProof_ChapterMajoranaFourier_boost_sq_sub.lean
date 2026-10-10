-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaFourier_boost_sq_sub
-- name    : BookProof.ChapterMajoranaFourier.boost_sq_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:54:37.719634+00:00
-- url     : https://prove2.me/theorems/1a7dece4-71d4-4303-9dbf-5907b9696a07
-- title:
--   `BookProof.ChapterMajoranaFourier.boost_sq_sub` (m q : ℝ) (hm : 0 ≤ m) (hq : 0 < q) : boostC m q ^ 2 - boostS m q ^ 2 = m / Ep m q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMajoranaFourier`.
--
--   `BookProof.ChapterMajoranaFourier.boost_sq_sub` (m q : ℝ) (hm : 0 ≤ m) (hq : 0 < q) : boostC m q ^ 2 - boostS m q ^ 2 = m / Ep m q
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMajoranaFourier.boost_sq_sub`.

-- Generated from ChapterMajoranaFourier.lean — theorem BookProof.ChapterMajoranaFourier.boost_sq_sub
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterMajoranaFourier
open BookProof.ChapterMajoranaFourier


open Matrix


open BookProof.ChapterA3

theorem BookProof.ChapterMajoranaFourier.boost_sq_sub (m q : ℝ) (hm : 0 ≤ m) (hq : 0 < q) :
    boostC m q ^ 2 - boostS m q ^ 2 = m / Ep m q := by sorry
