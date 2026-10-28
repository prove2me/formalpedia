-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_of_sigma_zero_components
-- name    : AvramDividend.Classical.generator_residual_continuousOn_of_sigma_zero_components
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:58:32.195896+00:00
-- url     : https://prove2.me/theorems/67981d42-887f-481d-8771-5934f081d4b3
-- title:
--   Generator residual is continuous from C1 local data and a continuous jump term when sigma is zero
-- statement:
--   When the Gaussian coefficient σ vanishes, the second-order differential term disappears from the spectrally negative Lévy generator. Consequently the discounted generator residual is continuous on a state set whenever the scale function W, its ordinary derivative W', and its compensated negative-jump integral are continuous there. This is the missing first-order counterpart of the Proved C2 generator-residual continuity lemma and is suitable for the bounded-variation branch.
-- source:
--   Avram, Palmowski, Pistorius (2007), Lemma 4, bounded-variation generator with no Gaussian component.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generator_residual_continuousOn_of_sigma_zero_components
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : X.σ = 0)
    (q : ℝ) (W : ℝ → ℝ) (s : Set ℝ)
    (hW : ContinuousOn W s)
    (hD : ContinuousOn (deriv W) s)
    (hJ : ContinuousOn
      (fun x : ℝ =>
        ∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)
      s) :
    ContinuousOn (fun x : ℝ => X.generator W x - q * W x) s := by sorry

end AvramDividend.Classical
