-- Prove2me | Theorems.Thm_BookProof_ChapterF6_mgT_apply_le
-- name    : BookProof.ChapterF6.mgT_apply_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T05:02:52.291493+00:00
-- url     : https://prove2.me/theorems/441798b4-b584-41cc-8bae-25c44bda4ddf
-- title:
--   `BookProof.ChapterF6.mgT_apply_le` (k : ℕ) (T : α →₀ ℕ) (s : List α) (y : α) : (mgT k T s) y ≤ T y + s.count y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF6`.
--
--   `BookProof.ChapterF6.mgT_apply_le` (k : ℕ) (T : α →₀ ℕ) (s : List α) (y : α) : (mgT k T s) y ≤ T y + s.count y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF6.mgT_apply_le`.

-- Generated from ChapterF6.lean — theorem BookProof.ChapterF6.mgT_apply_le
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6


open scoped BigOperators


variable {α : Type*} [DecidableEq α]

theorem BookProof.ChapterF6.mgT_apply_le (k : ℕ) (T : α →₀ ℕ) (s : List α) (y : α) :
    (mgT k T s) y ≤ T y + s.count y := by sorry
