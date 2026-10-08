-- Prove2me | Theorems.Thm_BookProof_SchrodingerCutoff_schrodingerOp_symmetric
-- name    : BookProof.SchrodingerCutoff.schrodingerOp_symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:33:57.627884+00:00
-- url     : https://prove2.me/theorems/98fde57e-247b-4f8e-9fe8-c26d10e934db
-- title:
--   The Lean 4 theorem `schrodingerOp_symmetric` in the `ChapterSchrodingerCutoffEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `schrodingerOp_symmetric` in the `ChapterSchrodingerCutoffEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSchrodingerCutoffEsa.lean

-- Generated from ChapterSchrodingerCutoffEsa.lean — theorem BookProof.SchrodingerCutoff.schrodingerOp_symmetric
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
open BookProof.SchrodingerCutoff



open MeasureTheory Filter Complex

theorem BookProof.SchrodingerCutoff.schrodingerOp_symmetric (V : ℝ → ℝ) (hV : Continuous V)
    (f g f' f'' g' g'' : ℝ → ℂ)
    (hf1 : ∀ x, HasDerivAt f (f' x) x) (hf2 : ∀ x, HasDerivAt f' (f'' x) x)
    (hg1 : ∀ x, HasDerivAt g (g' x) x) (hg2 : ∀ x, HasDerivAt g' (g'' x) x)
    (hf''c : Continuous f'') (hg''c : Continuous g'')
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    (∫ x, (starRingEnd ℂ) (schrodingerOp V f x) * g x)
      = ∫ x, (starRingEnd ℂ) (f x) * schrodingerOp V g x := by sorry
