-- Prove2me | Theorems.Thm_BookProof_SchrodingerCutoff_exists_scaled_cutoff
-- name    : BookProof.SchrodingerCutoff.exists_scaled_cutoff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:34:43.353827+00:00
-- url     : https://prove2.me/theorems/33284aa9-03ef-47d7-b384-4d2bd1917af9
-- title:
--   The Lean 4 theorem `exists_scaled_cutoff` in the `ChapterSchrodingerCutoffEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `exists_scaled_cutoff` in the `ChapterSchrodingerCutoffEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSchrodingerCutoffEsa.lean

-- Generated from ChapterSchrodingerCutoffEsa.lean — theorem BookProof.SchrodingerCutoff.exists_scaled_cutoff
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
import Definitions.Def_ChapterParityChirality
open BookProof.ChapterParityChirality
open BookProof.SchrodingerCutoff



open MeasureTheory Filter Complex

theorem BookProof.SchrodingerCutoff.exists_scaled_cutoff {C R : ℝ} (hC : ∀ y, |deriv chi y| ≤ C) (hR : 0 < R) :
    ∃ w wd : ℝ → ℝ, (∀ x, HasDerivAt w (wd x) x) ∧ Continuous w ∧ Continuous wd ∧
      (∀ x : ℝ, 2 * R < |x| → w x = 0) ∧ (∀ x : ℝ, 2 * R < |x| → wd x = 0) ∧
      (∀ x : ℝ, |x| ≤ R → w x = 1) ∧ (∀ x, |wd x| ≤ C / R) := by sorry
