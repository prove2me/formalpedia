-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux12b_original_jump_laplace_cutoff_convergence
-- name    : AvramDividend.Classical.avram_redux12b_original_jump_laplace_cutoff_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:35:20.369637+00:00
-- url     : https://prove2.me/theorems/303adb55-b277-4741-b3f2-108f1ee64561
-- title:
--   Actual jump and source Lévy exponential transforms converge under vanishing cutoff
-- statement:
--   As reciprocal cutoffs tend to zero, both sides of the finite-cutoff original jump Laplace transform converge to their full-jump target expressions at every natural horizon. This isolates the dominated/monotone convergence and bounded-variation integrability arguments from the finite-jump Poisson law.
-- source:
--   Faithful limiting step of original actual-jump Laplace identity 75bc3f76. Uses BV absolute jump variation, monotone convergence of the source ν integrals and dominated convergence of exponentials. Correct strict cutoff ensures y < -ε corresponds to original negative jumps of amplitude > ε, including Lévy-measure atoms at thresholds consistently.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_redux12b_original_jump_laplace_cutoff_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ n : ℕ,
      Tendsto (fun k : ℕ =>
        (∫ ω : Ω, Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) < (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal)) ∂P)) atTop (𝓝
        ((∫ ω : Ω, Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal)) ∂P))) ∧
      Tendsto (fun k : ℕ =>
        Real.exp (-((n : ℝ) *
        (∫ y in Iio (-(1 / ((k : ℝ) + 1))), (1 - Real.exp y) ∂X.ν)))) atTop (𝓝
        (Real.exp (-((n : ℝ) *
        (∫ y in Iio (0 : ℝ), (1 - Real.exp y) ∂X.ν))))) := by sorry
