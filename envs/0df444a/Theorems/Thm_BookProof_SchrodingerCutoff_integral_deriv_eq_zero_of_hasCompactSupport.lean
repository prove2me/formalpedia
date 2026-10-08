-- Prove2me | Theorems.Thm_BookProof_SchrodingerCutoff_integral_deriv_eq_zero_of_hasCompactSupport
-- name    : BookProof.SchrodingerCutoff.integral_deriv_eq_zero_of_hasCompactSupport
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:31:19.913328+00:00
-- url     : https://prove2.me/theorems/0ac053c1-8727-417e-a056-1ac8dce9d6bb
-- title:
--   The Lean 4 theorem `integral_deriv_eq_zero_of_hasCompactSupport` in the `ChapterSchrodingerCutoffEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `integral_deriv_eq_zero_of_hasCompactSupport` in the `ChapterSchrodingerCutoffEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSchrodingerCutoffEsa.lean

-- Generated from ChapterSchrodingerCutoffEsa.lean — theorem BookProof.SchrodingerCutoff.integral_deriv_eq_zero_of_hasCompactSupport
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
open BookProof.SchrodingerCutoff



open MeasureTheory Filter Complex

theorem BookProof.SchrodingerCutoff.integral_deriv_eq_zero_of_hasCompactSupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g g' : ℝ → E} (h : ∀ x, HasDerivAt g (g' x) x) (hc : Continuous g')
    (hs : HasCompactSupport g) : ∫ x, g' x = 0 := by sorry
