-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_route11_zero_cap_contact_positive_cash
-- name    : AvramDividend.Classical.avram_bv_route11_zero_cap_contact_positive_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T08:26:44.151203+00:00
-- url     : https://prove2.me/theorems/833cfa93-1790-4f3b-8f18-20de2a79d713
-- title:
--   BV zero-cap barrier has no payable right jumps but strictly positive genuine Stieltjes cash
-- statement:
--   For every Standing bounded-variation spectrally negative Levy process with finite negative jump activity, the zero-cap, zero-reserve barrier strategy is admissible, has no right dividend-payment jumps at time zero or strictly before ruin, yet earns strictly positive finite-horizon discounted Stieltjes cash. This combines three separately Proved original-source results and certifies that the unrestricted-cap stochastic verification target cannot disregard the continuous dividend component when the HJB interior is empty.
-- source:
--   Original authoritative 3296bf8a zero-cap validity audit. Source-exact Proved inputs: 7779a885 (zero-candidate actual cash counterexample), ce3a5c88 (zero-time right limit vanishes), 751e2dad (strict pre-ruin right jumps vanish). It isolates an actual logical obstruction, not a new axiom or hypothetical model.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_zero_candidate_finite_horizon_counterexample
import Theorems.Thm_AvramDividend_Classical_zero_cap_rightLimit_zero_at_origin
import Theorems.Thm_AvramDividend_Classical_zero_cap_no_right_dividend_jump_before_ruin

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_bv_route11_zero_cap_contact_positive_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    ∃ n : ℕ,
      IsAdmissibleLe X 0 0 (barrierStrategy X 0 0) ∧
      (∀ ω (t : ℝ≥0),
        (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X 0 (barrierStrategy X 0 0) ω) →
        rightLimit (barrierStrategy X 0 0) t ω =
          barrierStrategy X 0 0 t ω) ∧
      0 < (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) := by sorry
