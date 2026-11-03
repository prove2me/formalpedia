-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_BV_drift_envelope_branch_full_HJB_cash_bound
-- name    : AvramDividend.Classical.avram_chat07b_original_BV_drift_envelope_branch_full_HJB_cash_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:12:14.59199+00:00
-- url     : https://prove2.me/theorems/b23c7bb3-881b-4631-ad9e-04fcaf4cd73c
-- title:
--   Original complete BV dividend cash satisfies HJB bound on the sharp drift-envelope branch
-- statement:
--   On the original Standing finite-variation Lévy process, its full discounted dividendMeasure payment integral through every deterministic nonnegative horizon is controlled by ENNReal.ofReal(w x) whenever the independently established sharp source drift envelope x+T X.drift does not exceed w x. The total payout includes time zero, simultaneous jumps, and diffuse dividend components; this is the genuine envelope branch and leaves the complementary HJB case explicit.
-- source:
--   Original Prove2Me source-specific sharp BV complete Stieltjes expected drift bound UUID 23ddd713; canonical Avram Proposition 4(i) verification bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_complete_closed_horizon_sharp_expected_drift_budget
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_chat07b_original_BV_drift_envelope_branch_full_HJB_cash_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (w : ℝ → ℝ)
    (hEnvelope : x + (T : ℝ) * X.drift ≤ w x) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ⊓ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by sorry
