-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_infinite_activity_topcap_HJB_growth_purejump
-- name    : AvramDividend.Classical.avram_f6_original_infinite_activity_topcap_HJB_growth_purejump
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T20:54:45.34676+00:00
-- url     : https://prove2.me/theorems/e9a89c4a-888b-4212-b038-8a33d38b9831
-- title:
--   Actual infinite-activity purejump original topcap HJB exponential growth
-- statement:
--   Original standing infinite negative jump activity UBV Levy with authentic X.σ = 0, topcap and HJB candidate. Prove a genuine global exponential upper bound via original Levy generator, nonlocal stochastic analysis; retains all actual source assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_infinite_activity_topcap_HJB_growth_purejump
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
    (hInfinite : X.ν (Iio (0 : ℝ)) = ⊤)
    (hCase : X.σ = 0) :
    ∃ (θ K : ℝ), 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y) := by sorry
