-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_UBV_admissible_finitecap_physical_boundary_weight_zero
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_UBV_admissible_finitecap_physical_boundary_weight_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:06:10.786423+00:00
-- url     : https://prove2.me/theorems/4d743d57-5069-4e17-b1ab-603cdef2fa2b
-- title:
--   Original UBV finite-cap zero and cap physical occupation vanishes directly under admissibility
-- statement:
--   For the actual original unbounded-variation Lévy reserve under finite-cap IsAdmissibleLe and nonnegative initial capital, the discounted physical-time generator integral over zero and cap contact before the genuine ruin-bounded clock vanishes. The needed real cap and initial time bound are derived from the native control, including D(0)=0 and X(0)=0. The general sigma-finite physical-time measure gives zero mass to initial time. This makes no claim about dividend Stieltjes mass at either boundary.
-- source:
--   Direct original IsAdmissibleLe positive-time cap conjunct and source zero-time control/Levy identities; accepted original UBV endpoint occupation ff85326b-c871-4413-ae1e-992296ca2b64. No dependency on unavailable finite-cap theorem module 5063acfe.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_stopped_lebesgue_zero_cap_contact_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine UBV admissibility directly removes endpoint occupation for atomless physical time. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_UBV_admissible_finitecap_physical_boundary_weight_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (hx : 0 ≤ x) (hc : 0 ≤ c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] (hZeroMass : μ {0} = 0)
    (weight : ℝ≥0 → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0,
        if (t : ℝ≥0∞) < τ ω ∧
          (riskProcess X x D t ω = 0 ∨ riskProcess X x D t ω = c)
        then weight t ω else 0 ∂μ) = 0 := by sorry
