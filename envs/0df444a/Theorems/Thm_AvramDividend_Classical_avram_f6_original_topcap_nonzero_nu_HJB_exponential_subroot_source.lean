-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_topcap_nonzero_nu_HJB_exponential_subroot_source
-- name    : AvramDividend.Classical.avram_f6_original_topcap_nonzero_nu_HJB_exponential_subroot_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T19:55:34.826335+00:00
-- url     : https://prove2.me/theorems/c408da56-6d73-48d6-a983-7204e61d5661
-- title:
--   Remaining genuine nonzero-jump topcap HJB source: global exponential growth controlled below a true Laplace root
-- statement:
--   Under original standing UBV spectrally negative Lévy with ν ≠ 0, topcap and exact generator/gradient HJB inequalities, establish an authentic growth envelope for candidate w bounded by K e^(θ y), θ≥0, with a genuine positive Laplace root ψ(λ)=p>0 and θ<λ. This source analytic theorem is the precise missing mathematical input for the already Proved true original topcap expected DCT conditional on exponential moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_topcap_nonzero_nu_HJB_exponential_subroot_source
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
    ∃ (θ K p lam : ℝ), 0 ≤ θ ∧ 0 ≤ K ∧ 0 < p ∧ 0 < lam ∧ θ < lam ∧
      X.ψ lam = p ∧
      ∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y) := by sorry
