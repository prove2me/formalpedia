-- Prove2me | Theorems.Thm_BookProof_ChapterH6_sirk_error_tendsto_zero
-- name    : BookProof.ChapterH6.sirk_error_tendsto_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:22:04.710237+00:00
-- url     : https://prove2.me/theorems/b924bc2f-4397-4f2b-ad75-baad3f61eac6
-- title:
--   (C Dmin h nv : ℝ) (hh : 0 < h) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ m : ℕ in atTop, |sirkBound C Dmin h nv m| < ε
-- statement:
--   Lean 4 theorem `BookProof.ChapterH6.sirk_error_tendsto_zero` (module `BookProof.ChapterH6`), source chapter `BookProof/ChapterChapterH6.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH6.lean

-- Generated from ChapterH6.lean — theorem BookProof.ChapterH6.sirk_error_tendsto_zero
import Mathlib
import Definitions.Def_ChapterH6
open BookProof.ChapterH6
open Filter Topology

set_option maxHeartbeats 1000000 in

theorem BookProof.ChapterH6.sirk_error_tendsto_zero (C Dmin h nv : ℝ) (hh : 0 < h) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, |sirkBound C Dmin h nv m| < ε := by sorry
