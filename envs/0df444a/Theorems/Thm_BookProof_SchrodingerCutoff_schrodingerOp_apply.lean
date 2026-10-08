-- Prove2me | Theorems.Thm_BookProof_SchrodingerCutoff_schrodingerOp_apply
-- name    : BookProof.SchrodingerCutoff.schrodingerOp_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:31:23.025647+00:00
-- url     : https://prove2.me/theorems/53e04928-4dbc-4ef6-b35f-fb55383d6dcc
-- title:
--   The Lean 4 theorem `schrodingerOp_apply` in the `ChapterSchrodingerCutoffEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `schrodingerOp_apply` in the `ChapterSchrodingerCutoffEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSchrodingerCutoffEsa.lean

-- Generated from ChapterSchrodingerCutoffEsa.lean — theorem BookProof.SchrodingerCutoff.schrodingerOp_apply
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
open BookProof.SchrodingerCutoff



open MeasureTheory Filter Complex

theorem BookProof.SchrodingerCutoff.schrodingerOp_apply (V : ℝ → ℝ) (f f' f'' : ℝ → ℂ)
    (hf1 : ∀ x, HasDerivAt f (f' x) x) (hf2 : ∀ x, HasDerivAt f' (f'' x) x) (x : ℝ) :
    schrodingerOp V f x = -f'' x + (V x : ℂ) * f x := by sorry
