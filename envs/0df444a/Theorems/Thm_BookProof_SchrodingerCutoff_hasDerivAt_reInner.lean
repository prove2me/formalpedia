-- Prove2me | Theorems.Thm_BookProof_SchrodingerCutoff_hasDerivAt_reInner
-- name    : BookProof.SchrodingerCutoff.hasDerivAt_reInner
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:30:52.733988+00:00
-- url     : https://prove2.me/theorems/6ea8c9cd-961d-4fa0-8339-1dcc276fab5c
-- title:
--   The Lean 4 theorem `hasDerivAt_reInner` in the `ChapterSchrodingerCutoffEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hasDerivAt_reInner` in the `ChapterSchrodingerCutoffEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSchrodingerCutoffEsa.lean

-- Generated from ChapterSchrodingerCutoffEsa.lean — theorem BookProof.SchrodingerCutoff.hasDerivAt_reInner
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
open BookProof.SchrodingerCutoff



open MeasureTheory Filter Complex

theorem BookProof.SchrodingerCutoff.hasDerivAt_reInner (u u' u'' : ℝ → ℂ) (x : ℝ)
    (h1 : HasDerivAt u (u' x) x) (h2 : HasDerivAt u' (u'' x) x) :
    HasDerivAt (fun y => ((starRingEnd ℂ) (u y) * u' y).re)
      (‖u' x‖ ^ 2 + ((starRingEnd ℂ) (u x) * u'' x).re) x := by sorry
