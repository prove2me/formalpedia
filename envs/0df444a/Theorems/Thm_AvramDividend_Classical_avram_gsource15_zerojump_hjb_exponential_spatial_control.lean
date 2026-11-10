-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gsource15_zerojump_hjb_exponential_spatial_control
-- name    : AvramDividend.Classical.avram_gsource15_zerojump_hjb_exponential_spatial_control
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:39:40.828123+00:00
-- url     : https://prove2.me/theorems/9971fd6f-5a23-4095-ad13-a33c0186a2c7
-- title:
--   Exponential control of Gaussian zero-jump HJB spatial value and gradient
-- statement:
--   For the same spectrally negative Levy process with zero jump measure and nonzero Gaussian coefficient, an HJB supersolution with nonnegative value and gradient and C2 derivatives along a compact positive spatial interval has exponentially bounded w+w-prime between interval endpoints. This uses a proved generator curvature bound and a proved deterministic differential comparison, and imposes no stochastic Ito or reward conclusion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gsource15_zerojump_hjb_linear_curvature_majorant
import Theorems.Thm_AvramDividend_Classical_avram_gsource15_exponential_derivative_comparison
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gsource15_zerojump_hjb_exponential_spatial_control
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hw_nonneg : ∀ y ∈ Set.Icc a b, 0 ≤ w y)
    (hw_grad : ∀ y ∈ Set.Icc a b, 0 ≤ deriv w y)
    (hHJB : ∀ y ∈ Set.Icc a b, X.generator w y - q * w y ≤ 0)
    (hDer1 : ∀ y ∈ Set.Icc a b, HasDerivAt w (deriv w y) y)
    (hDer2 : ∀ y ∈ Set.Icc a b,
      HasDerivAt (deriv w) (iteratedDeriv 2 w y) y) :
    w b + deriv w b ≤
      Real.exp ((1 + 2 * (q + |X.c|) / X.σ ^ 2) * (b - a)) *
        (w a + deriv w a) := by
  sorry
