-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_infinite_cap_stopped_integrable_drift_nonpos
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_infinite_cap_stopped_integrable_drift_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:24:12.201312+00:00
-- url     : https://prove2.me/theorems/9df93f1b-7391-48eb-9505-8e8a1bad559e
-- title:
--   Actual infinite-cap original UBV stopped integrable generator drift is nonpositive
-- statement:
--   For the genuine source infinite-cap controlled reserve and any original ruin-dominated clock, an explicitly integrable signed real density satisfying the positive interior HJB sign has a finite nonpositive stopped integral under arbitrary deterministic s-finite physical-time measures, including a possible time-zero atom. This has no expectation-space L1 conclusion and no random dividend Stieltjes claim.
-- source:
--   Accepted original all-cap including time-zero stopped zero occupation source 644af487-db5d-4d41-995b-5576891a3013; original C = ⊤ and ruin-dominated clock. No upper cap boundary exists in this case.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_e_localise_original_infinite_cap_stopped_integrable_drift_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x ⊤ D)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ]
    (F : ℝ → ℝ)
    (hF : ∀ y : ℝ, 0 < y → F y ≤ 0)
    (hIntegrable : ∀ ω, Integrable
      (fun t : ℝ≥0 => if (t : ℝ≥0∞) < τ ω
        then F (riskProcess X x D t ω) else 0) μ) :
    ∀ᵐ ω ∂P,
      (∫ t : ℝ≥0, if (t : ℝ≥0∞) < τ ω
        then F (riskProcess X x D t ω) else 0 ∂μ) ≤ 0 := by sorry
