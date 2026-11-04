-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_true_stopped_integrable_generator_density_nonpos
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_true_stopped_integrable_generator_density_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:24:14.061195+00:00
-- url     : https://prove2.me/theorems/43cff21e-a1a0-4163-b9e4-acfb372c440a
-- title:
--   Nonpositive integrable original UBV generator density integrates nonpositively up to ruin-dominated clock
-- statement:
--   Source backed same-X,D generator density sign integrated at the original ruin-dominated clock over an arbitrary deterministic s-finite physical-time measure. Combine the already Proved zero and cap occupation statements with an explicit interior pointwise HJB sign F(y)<=0 and an explicit absolute Integrable hypothesis for the stopped density, yielding a genuine finite nonpositive real Bochner integral for P-almost every original path. Strictly positive times are used and the zero-time atom is excluded; no unsupported dividend Stieltjes sign or stopped local martingale UI conclusion is asserted.
-- source:
--   Source Proved zero occupation 644af487 and cap occupation cc500549; integral_nonpos_of_ae is a Mathlib consequence of the a.e. nonpositive integrable scalar density.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_e_localise_original_true_stopped_integrable_generator_density_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ]
    (F : ℝ → ℝ)
    (hF : ∀ y : ℝ, 0 < y → y < c → F y ≤ 0)
    (hIntegrable : ∀ ω, Integrable
      (fun t : ℝ≥0 => if 0 < t ∧ (t : ℝ≥0∞) < τ ω
        then F (riskProcess X x D t ω) else 0) μ) :
    ∀ᵐ ω ∂P,
      (∫ t : ℝ≥0, if 0 < t ∧ (t : ℝ≥0∞) < τ ω
        then F (riskProcess X x D t ω) else 0 ∂μ) ≤ 0 := by sorry
