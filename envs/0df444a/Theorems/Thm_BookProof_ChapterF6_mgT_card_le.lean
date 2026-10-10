-- Prove2me | Theorems.Thm_BookProof_ChapterF6_mgT_card_le
-- name    : BookProof.ChapterF6.mgT_card_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T05:02:39.026734+00:00
-- url     : https://prove2.me/theorems/f89f808b-37fe-45d3-a36c-79bfe3e0da11
-- title:
--   `BookProof.ChapterF6.mgT_card_le` (k : ℕ) (T : α →₀ ℕ) (s : List α) (hT : T.support.card ≤ k) : (mgT k T s).support.card ≤ k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF6`.
--
--   `BookProof.ChapterF6.mgT_card_le` (k : ℕ) (T : α →₀ ℕ) (s : List α) (hT : T.support.card ≤ k) : (mgT k T s).support.card ≤ k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF6.mgT_card_le`.

-- Generated from ChapterF6.lean — theorem BookProof.ChapterF6.mgT_card_le
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6


open scoped BigOperators


variable {α : Type*} [DecidableEq α]

theorem BookProof.ChapterF6.mgT_card_le (k : ℕ) (T : α →₀ ℕ) (s : List α) (hT : T.support.card ≤ k) :
    (mgT k T s).support.card ≤ k := by sorry
