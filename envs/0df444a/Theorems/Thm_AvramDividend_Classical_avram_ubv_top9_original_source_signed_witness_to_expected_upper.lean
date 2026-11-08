-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_source_signed_witness_to_expected_upper
-- name    : AvramDividend.Classical.avram_ubv_top9_original_source_signed_witness_to_expected_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:44:36.334472+00:00
-- url     : https://prove2.me/theorems/33c3d344-9fd4-4b47-86aa-8e476600d7d4
-- title:
--   Original UBV exact closed-clock expected upper from three centred physical stochastic sources
-- statement:
--   For an arbitrary actual source Lévy stopped reward with the genuine zero-clock right payment and closed Iic Stieltjes cash, three integrable centred stochastic components plus nonpositive signed generator/dividend remainders yield the original unmasked expected upper bound. The difficult input is a physically derived Ito-Meyer witness on the same stopping clock, to be discharged separately.
-- source:
--   Source-exact signed-witness-to-reward transfer under the exact hFsource and IsAdmissibleLe hypotheses of AvramDividend.Classical.avram_p4_f7_infinite_cap_integrable_clock_expected_upper 148b2516; uses proved avram_ubv_loc6_masked_original_stopped_reward_regular, proved avram_ubv_loc6_three_compensators_signed_remainder_auto_L1, proved F12 zero-event measurability and zero-clock mask dominance. It does not derive the stochastic witness from hBV/hgen; that is the stated outstanding premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_source_signed_witness_to_expected_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (Mc Ms Ml G R : Ω → ℝ)
    (hMcI : Integrable Mc P) (hMsI : Integrable Ms P)
    (hMlI : Integrable Ml P)
    (hMc0 : (∫ ω, Mc ω ∂P) = 0)
    (hMs0 : (∫ ω, Ms ω ∂P) = 0)
    (hMl0 : (∫ ω, Ml ω ∂P) = 0)
    (hG : ∀ᵐ ω ∂P, G ω ≤ 0)
    (hR : ∀ᵐ ω ∂P, R ω ≤ 0)
    (hIto : ∀ᵐ ω ∂P,
      (if σ ω = 0 then w x else F ω) ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + R ω) :
    (∫ ω, F ω ∂P) ≤ w x := by sorry
