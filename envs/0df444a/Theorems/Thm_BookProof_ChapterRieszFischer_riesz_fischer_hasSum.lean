-- Prove2me | Theorems.Thm_BookProof_ChapterRieszFischer_riesz_fischer_hasSum
-- name    : BookProof.ChapterRieszFischer.riesz_fischer_hasSum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T11:17:48.079964+00:00
-- url     : https://prove2.me/theorems/17cbe36d-9966-478f-a047-cf02efd0ff9f
-- title:
--   `BookProof.ChapterRieszFischer.riesz_fischer_hasSum` (f : Ell2) : HasSum (fun i => lp.single 2 i ((f : ℕ → ℝ) i)) f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterRieszFischer`.
--
--   `BookProof.ChapterRieszFischer.riesz_fischer_hasSum` (f : Ell2) : HasSum (fun i => lp.single 2 i ((f : ℕ → ℝ) i)) f
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterRieszFischer.riesz_fischer_hasSum`.

-- Generated from ChapterRieszFischer.lean — theorem BookProof.ChapterRieszFischer.riesz_fischer_hasSum
import Mathlib
import Definitions.Def_ChapterRieszFischer
open BookProof.ChapterRieszFischer


open Filter
open scoped ENNReal

theorem BookProof.ChapterRieszFischer.riesz_fischer_hasSum (f : Ell2) :
    HasSum (fun i => lp.single 2 i ((f : ℕ → ℝ) i)) f := by sorry
