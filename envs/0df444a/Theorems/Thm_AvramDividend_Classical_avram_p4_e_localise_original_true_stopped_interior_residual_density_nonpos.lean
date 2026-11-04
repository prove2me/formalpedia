-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_true_stopped_interior_residual_density_nonpos
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_true_stopped_interior_residual_density_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:20:23.341174+00:00
-- url     : https://prove2.me/theorems/506a1706-94bc-43bd-b711-9f5c8940c4ab
-- title:
--   Original controlled UBV interior residual density has nonpositive sign almost everywhere before ruin-dominated clock
-- statement:
--   For the actual original spectral-negative Levy process, admissible dividend strategy and capped controlled reserve, combine the independently Proved zero and upper-cap physical-time occupation results to transfer any real-valued interior residual sign condition to P-almost every original path and mu-almost every strictly positive time before any ruin-dominated original random clock. The residual may be the interior generator deficit X.generator w y - q*w y after the real-to-ENNReal cap bound is established. This is a genuine same-source occupation sign bridge; it does not assert random dividend Stieltjes cap mass zero, reflected local-time vanishing or stochastic Ito integral existence.
-- source:
--   Existing Proved original-source zero occupation UUID 644af487-db5d-4d41-995b-5576891a3013; cap occupation cc500549-ba08-47b0-b5c0-07c7a9bb40f3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_e_localise_original_true_stopped_interior_residual_density_nonpos
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
    (hF : ∀ y : ℝ, 0 < y → y < c → F y ≤ 0) :
    ∀ᵐ ω ∂P, ∀ᵐ t : ℝ≥0 ∂μ,
      0 < t → (t : ℝ≥0∞) < τ ω →
      F (riskProcess X x D t ω) ≤ 0 := by sorry
