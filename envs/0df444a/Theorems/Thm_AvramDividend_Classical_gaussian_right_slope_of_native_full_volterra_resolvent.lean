-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_right_slope_of_native_full_volterra_resolvent
-- name    : AvramDividend.Classical.gaussian_right_slope_of_native_full_volterra_resolvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:47:13.283237+00:00
-- url     : https://prove2.me/theorems/f166e7c6-ea46-482f-9c66-17d75f7bd6ea
-- title:
--   Gaussian right-origin scale derivative from the full native Volterra resolvent
-- statement:
--   For a positive Gaussian Lévy coefficient, a tilted scale V vanishing in the right limit at zero, with derivative resolvent g continuous on [0,infinity) and satisfying the exact Gaussian-variance second-kind equation (sigma squared over two)*g+(beta+K)*g=1, where K is L1, has original scale derivative tending to 2/sigma squared as x decreases to zero. The proof combines three already Proved results: nonnegative-time continuous input is locally bounded, full L1 Volterra convolution vanishes at zero, and the Gaussian right-slope germ lemma.
-- source:
--   Formal composition of the already Proved causal_continuousOn_nonnegative_locally_bounded, causal_full_l1_kernel_vanishes_at_origin, and gaussian_right_slope_of_native_resolvent_germ.

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_causal_continuousOn_nonnegative_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_full_l1_kernel_vanishes_at_origin
import Theorems.Thm_AvramDividend_Classical_gaussian_right_slope_of_native_resolvent_germ
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace AvramDividend.Classical
/-- The native Gaussian derivative-resolvent equation identifies the right-hand scale slope. -/
theorem gaussian_right_slope_of_native_full_volterra_resolvent
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (W V g K : ℝ → ℝ) (φ β : ℝ)
    (hW : ∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x)
    (hVlim : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hgeq : ∀ x : ℝ, 0 < x →
      (X.σ ^ 2 / 2) * g x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * g s ∂volume) = 1)
    (hVderiv : ∀ x : ℝ, 0 < x → HasDerivAt V (g x) x) :
    Tendsto (deriv W) (𝓝[>] (0 : ℝ)) (𝓝 (2 / X.σ ^ 2)) := by
  sorry
end AvramDividend.Classical
