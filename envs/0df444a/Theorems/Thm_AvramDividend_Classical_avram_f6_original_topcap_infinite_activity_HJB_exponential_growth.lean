-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_topcap_infinite_activity_HJB_exponential_growth
-- name    : AvramDividend.Classical.avram_f6_original_topcap_infinite_activity_HJB_exponential_growth
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T20:49:55.980766+00:00
-- url     : https://prove2.me/theorems/0184ed8f-a76d-47d8-98dd-ba607bd0c7d4
-- title:
--   Original infinite-jump-activity topcap HJB exponential upper growth source
-- statement:
--   For genuine source nonzero negative-jump infinite-intensity UBV standing Lévy, original topcap HJB generator ≤ q w and gradient ≥1, prove w has finite-rate global exponential growth. This is the remaining nonlocal analytic source after the finite-activity Gaussian ODE route.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_topcap_infinite_activity_HJB_exponential_growth
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
    (hwgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hInfinite : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∃ (θ K : ℝ), 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y) := by sorry
