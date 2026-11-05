-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_constant_strict_Fatou_payoff_grid
-- name    : AvramDividend.Classical.avram_p3_bv_original_constant_strict_Fatou_payoff_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:52:43.982893+00:00
-- url     : https://prove2.me/theorems/df0c3848-e78e-49f2-bdf6-2c4b399a2700
-- title:
--   Original strict stopped BV reward yields a measurable nonnegative L1 constant Fatou grid
-- statement:
--   The exact original stopped strict cash-and-terminal reward has an almost-everywhere equal measurable, nonnegative integrable representative. The constant sequence of this representative is an actual source-specific Fatou payoff grid satisfying all F_n measurability, nonnegativity, integrability and strict-payoff liminf premises. This leaves only the physical source pathwise mesh upper bound and compensated jump plus HJB signed expected mean to establish. It does not assume zero source residual, artificial boundary occupation or any uniform L1 mesh envelope.
-- source:
--   Proved avram_p3_bv_original_strict_reward_measurable_version; original source strict cash/terminal definitions; Filter.liminf constant

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_measurable_version

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- Original stopped strict cash plus terminal already supplies a
nonnegative integrable measurable (a.e.) constant Fatou payoff grid.
Only the genuine pathwise source inequality and compensated HJB drift
remain to be constructed separately. -/

theorem AvramDividend.Classical.avram_p3_bv_original_constant_strict_Fatou_payoff_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) :
    ∃ F : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        ENNReal.ofReal (
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0)) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by sorry
