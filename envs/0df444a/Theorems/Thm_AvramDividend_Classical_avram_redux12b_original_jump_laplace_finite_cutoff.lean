-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux12b_original_jump_laplace_finite_cutoff
-- name    : AvramDividend.Classical.avram_redux12b_original_jump_laplace_finite_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:29:15.302093+00:00
-- url     : https://prove2.me/theorems/5cd30d95-4934-488b-a710-1bf044355538
-- title:
--   Exact finite-cutoff negative-jump Laplace functional for original BV Lévy paths
-- statement:
--   For every natural horizon n and reciprocal natural cutoff, identify the original source-jump exponential functional of all negative jumps with amplitude at least the cutoff with the matching Lévy measure integral over negative jumps below the cutoff. This is a genuine original-path marked-jump law.
-- source:
--   Faithful finite-activity truncation of the original actual-jump Laplace identity 75bc3f76, based on Lévy marked-jump compensator / finite-cutoff jump measure. Correct strict cutoff ensures y < -ε corresponds to original negative jumps of amplitude > ε, including Lévy-measure atoms at thresholds consistently.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_redux12b_original_jump_laplace_finite_cutoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ (n k : ℕ),
      (∫ ω : Ω, Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) < (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal)) ∂P) =
      Real.exp (-((n : ℝ) *
        (∫ y in Iio (-(1 / ((k : ℝ) + 1))), (1 - Real.exp y) ∂X.ν))) := by sorry
