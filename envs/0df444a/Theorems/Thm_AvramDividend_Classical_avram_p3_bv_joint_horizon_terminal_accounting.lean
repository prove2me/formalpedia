-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_joint_horizon_terminal_accounting
-- name    : AvramDividend.Classical.avram_p3_bv_joint_horizon_terminal_accounting
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:52:04.719744+00:00
-- url     : https://prove2.me/theorems/d7254588-fbcb-4da8-ad7d-6ee8e2bba428
-- title:
--   Exact original BV closed-horizon cash plus signed surviving terminal bounded by strict cash and prepayment value
-- statement:
--   For a genuine original admissible dividend strategy at strictly positive finite horizon, almost surely the exact closed-horizon discounted Stieltjes cash plus the strict-survival post-rightpayment signed terminal is bounded by strictly pre-horizon cash plus the strict-survival prepayment candidate value. Strict survival and ruin/no-survival are handled separately; no original jump compensation is assumed.
-- source:
--   Proved P3 strict-survival horizon atom absorption and nonsurvival horizon cash equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_survival_horizon_atom_absorption
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_nonsurvival_horizon_cash_open
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_joint_horizon_terminal_accounting
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
        else 0) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0) := by sorry
