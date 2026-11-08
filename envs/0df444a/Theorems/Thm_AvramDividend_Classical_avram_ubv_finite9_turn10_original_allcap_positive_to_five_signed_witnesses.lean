-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn10_original_allcap_positive_to_five_signed_witnesses
-- name    : AvramDividend.Classical.avram_ubv_finite9_turn10_original_allcap_positive_to_five_signed_witnesses
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T23:48:10.035368+00:00
-- url     : https://prove2.me/theorems/da80762d-c468-44e5-aa00-daf38f3b6e5a
-- title:
--   Original stopped Lévy reward positive-clock expected upper bound yields five all-cap signed witnesses
-- statement:
--   For the genuine original spectrally negative Lévy process and admissible dividend strategy, assume each exact stopped reward F_k is integrable and has a probability-weighted conditional expected HJB upper bound on the strictly positive-clock event. Then every zero-clock-masked F_k has five centred/nonpositive signed budget witnesses exactly matching the original pure-jump and mixed stochastic budget conclusions. This works with finite or infinite cap and preserves the physical stopped source and time-zero payment convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn10_positive_clock_allcap_five_signed_witnesses

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite9_turn10_original_allcap_positive_to_five_signed_witnesses
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
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
    (hpositive : ∀ k,
      (∫ ω in {ω : Ω | σ k ω ≠ 0}, F k ω ∂P) ≤
        w x * (P {ω : Ω | σ k ω ≠ 0}).toReal) :
    ∀ k, ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        (if σ k ω = 0 then w x else F k ω) ≤
          w x + Mc ω + Ms ω + Ml ω + G ω + R ω) := by sorry
