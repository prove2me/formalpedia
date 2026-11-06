-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
-- name    : AvramDividend.Classical.avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:51:51.297302+00:00
-- url     : https://prove2.me/theorems/605f662e-38d3-41fc-a154-41e93e3aaa82
-- title:
--   Original BV strict cash-prefix payoff grids are measurable, nonnegative, L1 and satisfy Fatou
-- statement:
--   For the actual spectrally negative Levy X and original admissible D, positive T and an antitone cofinal strict horizon mesh with 0<delta_n<=T, the original strict pre-ruin Stieltjes cash over Iio(T-delta_n) plus the unchanged pre-rightpayment surviving terminal at T is measurable and integrable for every n, pointwise nonnegative, and dominates the exact original strict payoff in the ENNReal lower liminf. Uses original strict cash measurability, finite-horizon L1, BV original prebudget L1, positive actual terminal and the new source-exact Fatou lemma fe957018. It does not claim any compensated source martingale or signed drift inequality.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_cash_terminal_fatou_liminf

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδle : ∀ n, δ n ≤ T)
    (hδanti : Antitone δ) (hδ : Tendsto δ atTop (𝓝 0)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
       else 0)
    (∀ n, Measurable (F n) ∧ Integrable (F n) P ∧
      (∀ ω, 0 ≤ F n ω)) ∧
    (∀ ω, ENNReal.ofReal
      ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
       (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)) ≤
      liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by sorry
