-- Prove2me | Theorems.Thm_BookProof_ChapterF6_mgStep_card_le
-- name    : BookProof.ChapterF6.mgStep_card_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T05:02:03.388986+00:00
-- url     : https://prove2.me/theorems/cbe55295-e8d6-4431-a74d-04545d6d8f4b
-- title:
--   `BookProof.ChapterF6.mgStep_card_le` (k : ℕ) (T : α →₀ ℕ) (x : α) (hT : T.support.card ≤ k) : (mgStep k T x).support.card ≤ k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF6`.
--
--   `BookProof.ChapterF6.mgStep_card_le` (k : ℕ) (T : α →₀ ℕ) (x : α) (hT : T.support.card ≤ k) : (mgStep k T x).support.card ≤ k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF6.mgStep_card_le`.

-- Generated from ChapterF6.lean — theorem BookProof.ChapterF6.mgStep_card_le
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6


open scoped BigOperators


variable {α : Type*} [DecidableEq α]

theorem BookProof.ChapterF6.mgStep_card_le (k : ℕ) (T : α →₀ ℕ) (x : α) (hT : T.support.card ≤ k) :
    (mgStep k T x).support.card ≤ k := by sorry
