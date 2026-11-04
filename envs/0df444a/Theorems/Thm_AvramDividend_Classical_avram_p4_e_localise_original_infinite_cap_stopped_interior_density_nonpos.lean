-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_infinite_cap_stopped_interior_density_nonpos
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_infinite_cap_stopped_interior_density_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:23:47.129437+00:00
-- url     : https://prove2.me/theorems/976d5892-3928-47e0-bd4e-d57a65c24b0a
-- title:
--   Original infinite-cap UBV generator density is nonpositive a.e. even at physical-time zero
-- statement:
--   At infinite admissibility cap C=top, source zero-occupation holds up to any ruin-dominated actual original clock, including at any physical-time atom t=0. Thus a positive-interior nonpositive generator deficit is nonpositive almost everywhere without any cap-contact exclusion or cap bound conversion. This does not annul dividend Stieltjes mass or local time.
-- source:
--   Accepted original all-cap including time-zero stopped zero occupation source 644af487-db5d-4d41-995b-5576891a3013; original C = ⊤ and ruin-dominated clock. No upper cap boundary exists in this case.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_e_localise_original_infinite_cap_stopped_interior_density_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x ⊤ D)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ]
    (F : ℝ → ℝ)
    (hF : ∀ y : ℝ, 0 < y → F y ≤ 0) :
    ∀ᵐ ω ∂P, ∀ᵐ t : ℝ≥0 ∂μ,
      (t : ℝ≥0∞) < τ ω →
      F (riskProcess X x D t ω) ≤ 0 := by sorry
