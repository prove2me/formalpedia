-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generatorJump_continuousOn_compact_of_uniform_BV_envelope
-- name    : AvramDividend.Classical.avram_wave4_p3_generatorJump_continuousOn_compact_of_uniform_BV_envelope
-- status  : Open
-- author  : @WillR
-- created : 2026-10-31T17:09:19.830758+00:00
-- url     : https://prove2.me/theorems/d858dc97-1bc3-4a04-accd-ccfb71ad8430
-- title:
--   Uniform BV first-moment envelope gives generic compensated-generator jump continuity
-- statement:
--   For the true spectrally negative Lévy jump measure in the bounded-variation case, every globally monotone real test function whose compensated kernel has one uniform compact-state first-order Lévy envelope and is almost everywhere continuous in the state has a continuous jump-generator integral on the compact state interval. The result is independent of the scale-function predicate and therefore applies to the piecewise dividend candidate once its nontrivial envelope and atomless crossing-of-zero continuity are established. It does not assume or conclude endpoint harmonicity and does not assert generator integrability without its stated envelope.
-- source:
--   BoundedVariation_min_one_abs_integrable (Proved UUID 1f8249f1); dominated integral continuity (Proved); generic P3 C2 proof 0d8985c3 adapted to the first-order BV moment; Avram, Palmowski, Pistorius (2007) Standing (3.3) and KKR (2013) generator-domain caution. Positive-barrier endpoint continuity research; no overlap with Chat05 harmonicity or Chat06 stochastic verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_generatorJump_continuousOn_compact_of_uniform_BV_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation)
    (f : ℝ → ℝ) (hmono : Monotone f)
    (l u : ℝ)
    (hlinear : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y ∈ Iio (0 : ℝ),
        ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤
          C * min 1 |y|)
    (hjump : ∀ x ∈ Icc l u,
      ∀ᵐ y ∂(X.ν.restrict (Iio 0)),
        ContinuousWithinAt
          (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand f z y)
          (Icc l u) x) :
    ContinuousOn
      (fun x : ℝ =>
        ∫ y : ℝ, SpectrallyNegativeLevy.generatorIntegrand f x y
          ∂(X.ν.restrict (Iio 0)))
      (Icc l u) := by sorry
