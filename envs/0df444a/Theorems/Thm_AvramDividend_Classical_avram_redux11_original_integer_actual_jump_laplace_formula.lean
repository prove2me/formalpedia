-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux11_original_integer_actual_jump_laplace_formula
-- name    : AvramDividend.Classical.avram_redux11_original_integer_actual_jump_laplace_formula
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:14:10.725869+00:00
-- url     : https://prove2.me/theorems/75bc3f76-b88e-427e-a0f5-c3c38e444175
-- title:
--   Original BV actual negative-jump count sum has the source Lévy Laplace law at every integer horizon
-- statement:
--   Prove the exact exponential Laplace transform of the genuine original-source total of negative left jumps at every natural horizon and tilt one. The total is the actual pathwise ENNReal negative-jump sum, with source Lévy measure ν, original Ω/P/filtration, and no auxiliary Poisson process. This supplies the stochastic characteristic identification missing from the proved conditional BV global-path decomposition.
-- source:
--   Original spectrally negative BV Lévy jump functional Laplace identity; upstream P2/P3 bottleneck for source drift-minus-actual-jumps identity. Source characteristic convention must be preserved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_redux11_original_integer_actual_jump_laplace_formula
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ n : ℕ,
      (∫ ω : Ω, Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal)) ∂P) =
      Real.exp (-((n : ℝ) *
        (∫ y in Iio (0 : ℝ), (1 - Real.exp y) ∂X.ν))) := by sorry
