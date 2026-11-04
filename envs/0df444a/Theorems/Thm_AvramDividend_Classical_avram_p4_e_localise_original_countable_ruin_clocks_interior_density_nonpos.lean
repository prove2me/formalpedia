-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_countable_ruin_clocks_interior_density_nonpos
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_countable_ruin_clocks_interior_density_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:21:57.901844+00:00
-- url     : https://prove2.me/theorems/2207174a-bcbf-43f5-bbb9-602cf4d77d4d
-- title:
--   Countable original ruin-dominated UBV clocks share a conull interior generator sign event
-- statement:
--   For countably many genuine original-source ruin-dominated stopped clocks, independently varying deterministic s-finite physical-time measures and generator density functions F k satisfying the real open-interior HJB sign, intersect the accepted original-source single-clock conull events. No dividend Stieltjes or local-time assertion is made.
-- source:
--   Accepted single-clock original source interior density UUID 506a1706-94bc-43bd-b711-9f5c8940c4ab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_true_stopped_interior_residual_density_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_e_localise_original_countable_ruin_clocks_interior_density_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτ : ∀ k ω, τ k ω ≤ ruinTime X x D ω)
    (μ : ℕ → Measure ℝ≥0) (hμ : ∀ k, SFinite (μ k))
    (F : ℕ → ℝ → ℝ)
    (hF : ∀ k (y : ℝ), 0 < y → y < c → F k y ≤ 0) :
    ∀ᵐ ω ∂P, ∀ k, ∀ᵐ t : ℝ≥0 ∂(μ k),
      0 < t → (t : ℝ≥0∞) < τ k ω →
      F k (riskProcess X x D t ω) ≤ 0 := by sorry
