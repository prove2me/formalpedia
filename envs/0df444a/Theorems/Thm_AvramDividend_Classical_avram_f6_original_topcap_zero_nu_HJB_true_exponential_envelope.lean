-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_topcap_zero_nu_HJB_true_exponential_envelope
-- name    : AvramDividend.Classical.avram_f6_original_topcap_zero_nu_HJB_true_exponential_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:39:43.971177+00:00
-- url     : https://prove2.me/theorems/ee23e02d-1e64-4dbc-b22c-5081b8e018f4
-- title:
--   Original zero-jump topcap HJB candidate is positive and admits genuine exponential envelope
-- statement:
--   Under source zero Levy measure, unbounded variation, topcap and genuine smooth HJB hypotheses, the actual candidate w has θ,K≥0 with w≥0 on positive reserves and global upper bound w≤K exp(θ y). Combines existing Proved source exponential and gradient lemmas.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_topcap_zero_nu_HJB_true_exponential_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hTop : C = ⊤) (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0)) (hwneg : ∀ y < 0, w y = 0)
    (hwsmooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwgen : ∀ y, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      (∀ y : ℝ, 0 ≤ y → 0 ≤ w y) ∧
      (∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y)) := by sorry
