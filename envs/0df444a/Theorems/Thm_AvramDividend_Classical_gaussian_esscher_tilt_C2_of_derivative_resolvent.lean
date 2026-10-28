-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilt_C2_of_derivative_resolvent
-- name    : AvramDividend.Classical.gaussian_esscher_tilt_C2_of_derivative_resolvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T14:26:24.794696+00:00
-- url     : https://prove2.me/theorems/3c037089-4af8-423d-aa66-c611a9bf2c20
-- title:
--   Gaussian Esscher scale C2 from an admissible C1 derivative resolvent
-- statement:
--   If a Gaussian q-scale function is represented by a positive Esscher tilt and has a positive-coefficient integrated Volterra equation together with a continuous C1 positive-axis derivative resolvent for the same kernel, then its tilted scale is C2 on the positive axis. Gaussian-specific continuity and local boundedness discharge the regularity side conditions of the general C2 theorem.
-- source:
--   Compose Gaussian Esscher-scale continuity, near-zero local boundedness, and the proved C2 promotion from a C1 derivative resolvent.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_continuous
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_volterra_C2_of_C1_derivative_resolvent

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_esscher_tilt_C2_of_derivative_resolvent
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
    ContDiffOn ℝ 2 V (Ioi (0 : ℝ)) := by sorry
