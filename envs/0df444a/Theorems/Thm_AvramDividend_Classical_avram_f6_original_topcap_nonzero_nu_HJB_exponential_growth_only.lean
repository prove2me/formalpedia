-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_topcap_nonzero_nu_HJB_exponential_growth_only
-- name    : AvramDividend.Classical.avram_f6_original_topcap_nonzero_nu_HJB_exponential_growth_only
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T20:34:23.456495+00:00
-- url     : https://prove2.me/theorems/bb94bb2a-3852-42bb-b19b-2e4e9e936aaa
-- title:
--   Genuine topcap nonzero-jump HJB candidate global exponential bound, analytic source
-- statement:
--   Prove a genuine global exponential upper bound for the original HJB candidate w, on the positive half-line under original standing unbounded-variation spectrally negative Lévy with nonzero jump measure, generator ≤ q w and gradient ≥1. This is the analytic source needed for original nonzero-jump topcap expectation; authentic ψ positive roots are handled independently.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_topcap_nonzero_nu_HJB_exponential_growth_only
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hTop : C = ⊤) (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0)) (hwneg : ∀ y < 0, w y = 0)
    (hwsmooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwgen : ∀ y, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∃ (θ K : ℝ), 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y) := by sorry
