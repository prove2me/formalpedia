-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_source_F_measurable_L1_liminf
-- name    : AvramDividend.Classical.avram_p3_grid4_original_strict_source_F_measurable_L1_liminf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:26:45.748387+00:00
-- url     : https://prove2.me/theorems/603764ec-f80d-4712-ab54-b6224448aeb4
-- title:
--   Original bounded-variation strict horizon nonnegative integrable Fatou payoff family
-- statement:
--   For the original spectrally negative bounded-variation Levy process X and admissible dividend D, construct one common real payoff family F whose each member is measurable, integrable and nonnegative almost surely, and whose ENNReal liminf dominates the exact original strict pre-horizon discounted Stieltjes dividends plus surviving pre-right-payment horizon terminal. This packages the already Proved original constant strict payoff construction into the exact first and fifth certificate conjuncts without any assumed signed budget, preserving time-zero and horizon atoms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_strict_source_F_measurable_L1_liminf
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
      (∀ n, Measurable (F n) ∧ Integrable (F n) P ∧ 0 ≤ᵐ[P] F n) ∧
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
