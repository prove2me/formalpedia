-- Prove2me | Theorems.Thm_BookProof_ChapterF6_mgSum_ge_card
-- name    : BookProof.ChapterF6.mgSum_ge_card
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T05:04:36.822596+00:00
-- url     : https://prove2.me/theorems/4d0d6f82-c4a6-489f-8d57-a39696a0acb2
-- title:
--   `BookProof.ChapterF6.mgSum_ge_card` (T : α →₀ ℕ) : T.support.card ≤ mgSum T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF6`.
--
--   `BookProof.ChapterF6.mgSum_ge_card` (T : α →₀ ℕ) : T.support.card ≤ mgSum T
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF6.mgSum_ge_card`.

-- Generated from ChapterF6.lean — theorem BookProof.ChapterF6.mgSum_ge_card
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6


open scoped BigOperators


variable {α : Type*} [DecidableEq α]

theorem BookProof.ChapterF6.mgSum_ge_card (T : α →₀ ℕ) : T.support.card ≤ mgSum T := by sorry
