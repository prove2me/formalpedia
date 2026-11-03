-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_same_measure_finite_horizon_inner_and_outer_real_integrability
-- name    : AvramDividend.Classical.avram_wave7_03_original_same_measure_finite_horizon_inner_and_outer_real_integrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:44:13.751971+00:00
-- url     : https://prove2.me/theorems/f1fd38c4-1f47-4159-bd47-66d00826f6ee
-- title:
--   Original source finite stopped horizons have genuine inner real Stieltjes integrability on every path and outer L1(P)
-- statement:
--   For each actual cap-admissible dividend strategy D and nonnegative discount q, every finite nonnegative stopped payment horizon has an integrable real discounted Stieltjes factor against the exact source dividendMeasure on paymentTimes(ruinTime)∩Iic T for every ω. Simultaneously the resulting genuine real signed finite-horizon Stieltjes cash function is L1 on the original probability measure P. Pathwise source mass finiteness, Borel measurability and positivity on the exact set justify the inner claim, and an already remotely proved original L1 theorem proves the outer claim. No assumptions of additional finite mass, conditional expectation, or substitute sample space are needed; the origin right-limit dividend atom, continuous cash and all strict pre-ruin times remain present.
-- source:
--   Proved dividendMeasure_paymentWindow_finite_of_strategy 6f41c374, paymentTimes_measurable 88dafb7f, discounted_stieltjes_integrableOn_of_finite_measure f70331c8, and original finite horizon real signed L1 theorem d69fc868.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_paymentWindow_finite_of_strategy
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_integrableOn_of_finite_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_signed_stieltjes_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_same_measure_finite_horizon_inner_and_outer_real_integrability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    (∀ ω : Ω, IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ))
      (dividendMeasure D ω)) ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P := by sorry
