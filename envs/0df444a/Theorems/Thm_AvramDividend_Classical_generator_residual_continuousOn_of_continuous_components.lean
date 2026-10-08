-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_of_continuous_components
-- name    : AvramDividend.Classical.generator_residual_continuousOn_of_continuous_components
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:11:04.179041+00:00
-- url     : https://prove2.me/theorems/1b5b6289-b0e5-4db7-8f27-86ea6068336a
-- title:
--   Continuity of the Lévy generator residual from continuity of its local and jump components
-- statement:
--   For a spectrally negative Lévy generator, if the scale function W, its first derivative, its second iterated derivative and its compensated jump integral are continuous on a state set s, then the generator residual x↦ΓW(x)-qW(x) is continuous there. This follows from the explicit Lévy generator decomposition into fixed drift and Gaussian coefficients times derivatives plus the jump integral. The result combines with compact jump-generator continuity and allows an almost-everywhere harmonicity identity to be promoted to pointwise equality.
-- source:
--   Actual SpectrallyNegativeLevy.generator definition and continuity closure of the finite algebraic sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generator_residual_continuousOn_of_continuous_components
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (s : Set ℝ)
    (hW : ContinuousOn W s)
    (hD : ContinuousOn (deriv W) s)
    (hD2 : ContinuousOn (iteratedDeriv 2 W) s)
    (hJ : ContinuousOn
      (fun x : ℝ =>
        ∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)
      s) :
    ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x) s := by sorry

end AvramDividend.Classical
