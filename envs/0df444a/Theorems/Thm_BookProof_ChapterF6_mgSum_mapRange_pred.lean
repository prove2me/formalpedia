-- Prove2me | Theorems.Thm_BookProof_ChapterF6_mgSum_mapRange_pred
-- name    : BookProof.ChapterF6.mgSum_mapRange_pred
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T05:04:42.602974+00:00
-- url     : https://prove2.me/theorems/5d435855-80c9-4afa-b796-2c5604418449
-- title:
--   `BookProof.ChapterF6.mgSum_mapRange_pred` (T : α →₀ ℕ) : mgSum (T.mapRange (fun n => n - 1) (by norm_num)) = mgSum T - T.support.card
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF6`.
--
--   `BookProof.ChapterF6.mgSum_mapRange_pred` (T : α →₀ ℕ) : mgSum (T.mapRange (fun n => n - 1) (by norm_num)) = mgSum T - T.support.card
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF6.mgSum_mapRange_pred`.

-- Generated from ChapterF6.lean — theorem BookProof.ChapterF6.mgSum_mapRange_pred
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6


open scoped BigOperators


variable {α : Type*} [DecidableEq α]

theorem BookProof.ChapterF6.mgSum_mapRange_pred (T : α →₀ ℕ) :
    mgSum (T.mapRange (fun n => n - 1) (by norm_num)) = mgSum T - T.support.card := by sorry
