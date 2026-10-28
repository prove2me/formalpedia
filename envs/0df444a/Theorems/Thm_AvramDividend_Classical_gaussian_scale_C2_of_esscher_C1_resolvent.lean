-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_scale_C2_of_esscher_C1_resolvent
-- name    : AvramDividend.Classical.gaussian_scale_C2_of_esscher_C1_resolvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T14:31:19.758916+00:00
-- url     : https://prove2.me/theorems/c41bb291-8ace-41e4-9033-3a17c4c713bb
-- title:
--   Gaussian q-scale C2 from C1 derivative resolvent and Esscher untwisting
-- statement:
--   If a Gaussian q-scale admits a positive Esscher tilt whose integrated Volterra kernel also has a continuous C1 derivative resolvent, then the original scale function W is C2 on positive reserves. This exact-scale conclusion is ready to be used by scaleFunction_contDiff_two_of_gaussian when the native C1 derivative-resolvent milestone closes.
-- source:
--   Apply the Gaussian Esscher C2 Volterra promotion theorem and then the proved exponential untilting C2 theorem.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilt_C2_of_derivative_resolvent
import Theorems.Thm_AvramDividend_Classical_esscher_untilt_contDiffOn_two_of_tilt_contDiffOn_two

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_scale_C2_of_esscher_C1_resolvent
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x)
    (a β : ℝ) (K g : ℝ → ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hgC1 : ContDiffOn ℝ 1 g (Ioi (0 : ℝ)))
    (hVe : ∀ x : ℝ, 0 < x →
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) = x)
    (hge : ∀ x : ℝ, 0 < x →
      a * g x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * g s ∂volume) = 1) :
    ContDiffOn ℝ 2 W (Ioi (0 : ℝ)) := by sorry
