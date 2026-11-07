-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn42_original_fatou_family_to_single_strict_signed_source
-- name    : AvramDividend.Classical.avram_bv_env3_turn42_original_fatou_family_to_single_strict_signed_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:18:38.052895+00:00
-- url     : https://prove2.me/theorems/6647e75c-51b3-4e92-8c9d-eeeb3b8573ca
-- title:
--   Original BV strict stopped reward receives a single integrable nonpositive signed residual from its physical Fatou grid
-- statement:
--   The actual original strict stopped dividend cash plus survival terminal has an integrable nonnegative representative. Physical signed finite-grid Fatou bounds therefore yield one integrable signed residual of nonpositive expectation that dominates the exact strict reward pathwise, by the accepted original-process L1 reward and generic signed Fatou witness theorem.
-- source:
--   Avram BV original physical strict reward L1 theorem 221852bf and signed Fatou residual witness theorem 67696edf, with only the displayed physical F/M/B grid hypotheses. Independent reduction of original strict source 9bd41781 and envelope c8770486.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_L1_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_signed_fatou_integrable_residual_witness
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn42_original_fatou_family_to_single_strict_signed_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 < q) (T : ℝ) (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (F M B : ℕ → Ω → ℝ)
    (hFm : ∀ n, Measurable (F n))
    (hFi : ∀ n, Integrable (F n) P)
    (hFn : ∀ n, 0 ≤ᵐ[P] F n)
    (hR : ∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
      (∫ ω, M n ω + B n ω ∂P) ≤ 0)
    (hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + (M n ω + B n ω))
    (hFatou : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      ENNReal.ofReal (
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)) ≤
      liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    ∃ Z : Ω → ℝ,
      Integrable Z P ∧ (∫ ω, Z ω ∂P) ≤ 0 ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0) ≤ w x + Z ω) := by sorry
