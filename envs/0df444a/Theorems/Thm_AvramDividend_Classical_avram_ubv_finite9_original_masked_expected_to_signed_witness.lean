-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_masked_expected_to_signed_witness
-- name    : AvramDividend.Classical.avram_ubv_finite9_original_masked_expected_to_signed_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:22:30.167448+00:00
-- url     : https://prove2.me/theorems/e1e61369-f98b-4613-85b0-eb2be37f8d22
-- title:
--   Original capped stopped masked expectation yields three genuine centred signed witnesses
-- statement:
--   For the actual capped original Lévy dividend source with a bounded stopped clock and post-right-payment physical reserve, if the zero-stopping-clock-masked discounted candidate payoff plus inclusive dividend cash has expected value at most the initial candidate value for each stopped subclock, then it admits three integrable mean-zero witnesses and two nonpositive remainder functions satisfying the source-exact signed budget. The first witness is the centred masked payoff and the remaining components are zero. This identifies the genuinely missing stochastic mathematical step as the masked original expected bound rather than witness existence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_rightcont_stopping_zero_mask_integrable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_original_masked_expected_to_signed_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hMaskedUpper : ∀ k,
      (∫ ω, (if σ k ω = 0 then w x else F k ω) ∂P) ≤ w x) :
    ∀ k, ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        (if σ k ω = 0 then w x else F k ω) ≤
          w x + Mc ω + Ms ω + Ml ω + G ω + R ω) := by sorry
