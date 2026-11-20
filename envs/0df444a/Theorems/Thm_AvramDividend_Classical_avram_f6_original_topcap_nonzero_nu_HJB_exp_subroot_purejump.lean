-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_topcap_nonzero_nu_HJB_exp_subroot_purejump
-- name    : AvramDividend.Classical.avram_f6_original_topcap_nonzero_nu_HJB_exp_subroot_purejump
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T20:01:45.121547+00:00
-- url     : https://prove2.me/theorems/4b99158c-d96f-496f-9fa1-4b436b091359
-- title:
--   Original nonzero-jump purejump topcap HJB global exponential subroot growth
-- statement:
--   Preserve the actual original standing spectrally negative Levy X with ν≠0, its true ψ, topcap HJB generator/gradient assumptions. Establish an exponential growth envelope w(y)≤Kexp(θy) and authentic ψ(λ)=p>0 with θ<λ in this genuine Gaussian or purejump branch. The two branches require distinct stochastic generator comparison methods; not a fabricated expectation or witness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_topcap_nonzero_nu_HJB_exp_subroot_purejump
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
    (hSigma : X.σ = 0) :
    ∃ (θ K p lam : ℝ), 0 ≤ θ ∧ 0 ≤ K ∧ 0 < p ∧ 0 < lam ∧ θ < lam ∧
      X.ψ lam = p ∧
      ∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y) := by sorry
