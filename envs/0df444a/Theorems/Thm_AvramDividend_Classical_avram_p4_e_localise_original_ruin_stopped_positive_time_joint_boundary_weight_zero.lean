-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_stopped_positive_time_joint_boundary_weight_zero
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_ruin_stopped_positive_time_joint_boundary_weight_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:02:47.224778+00:00
-- url     : https://prove2.me/theorems/e9e42507-ea81-49ef-80c6-5fe70694828c
-- title:
--   Exact original ruin-stopped generator physical-time boundary weights vanish at zero and finite cap
-- statement:
--   Under the actual original-filtration UBV Lévy process and admissible capped dividend strategy, combine two already Proved genuine source occupation theorems. For any ruin-dominated original random clock τ and any deterministic s-finite physical-time measure μ, the μ-integral of an arbitrary nonnegative possibly infinite weight supported on strictly positive times t<τ at which the controlled reserve equals either 0 or the real cap c vanishes P-almost surely. The restriction 0<t is indispensable because an arbitrary μ may charge the initial instant at the cap. This does not identify or annul path-dependent dividend Stieltjes mass or cap local time; it only permits generator and intensity density terms to be evaluated in the open HJB interior.
-- source:
--   Proved original source 644af487 zero occupation, cc500549 cap occupation; user P4-E original Ito localisation task.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_e_localise_original_ruin_stopped_positive_time_joint_boundary_weight_zero
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
    (weight : ℝ≥0 → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0, if 0 < t ∧ (t : ℝ≥0∞) < τ ω ∧
         (riskProcess X x D t ω = 0 ∨ riskProcess X x D t ω = c)
         then weight t ω else 0 ∂μ) = 0 := by sorry
