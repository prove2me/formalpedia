-- Prove2me | Theorems.Thm_BookProof_ChapterF6_mgStep_apply_le
-- name    : BookProof.ChapterF6.mgStep_apply_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T05:02:25.142453+00:00
-- url     : https://prove2.me/theorems/64d22a6e-584c-43b2-ae78-529e684d8a6f
-- title:
--   `BookProof.ChapterF6.mgStep_apply_le` (k : ℕ) (T : α →₀ ℕ) (x y : α) : (mgStep k T x) y ≤ T y + (if y = x then 1 else 0)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF6`.
--
--   `BookProof.ChapterF6.mgStep_apply_le` (k : ℕ) (T : α →₀ ℕ) (x y : α) : (mgStep k T x) y ≤ T y + (if y = x then 1 else 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF6.mgStep_apply_le`.

-- Generated from ChapterF6.lean — theorem BookProof.ChapterF6.mgStep_apply_le
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6


open scoped BigOperators


variable {α : Type*} [DecidableEq α]

theorem BookProof.ChapterF6.mgStep_apply_le (k : ℕ) (T : α →₀ ℕ) (x y : α) :
    (mgStep k T x) y ≤ T y + (if y = x then 1 else 0) := by sorry
