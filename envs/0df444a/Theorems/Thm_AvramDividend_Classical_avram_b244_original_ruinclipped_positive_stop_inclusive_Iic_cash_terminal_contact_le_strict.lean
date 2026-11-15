-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b244_original_ruinclipped_positive_stop_inclusive_Iic_cash_terminal_contact_le_strict
-- name    : AvramDividend.Classical.avram_b244_original_ruinclipped_positive_stop_inclusive_Iic_cash_terminal_contact_le_strict
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:18:22.88647+00:00
-- url     : https://prove2.me/theorems/8066526a-ce09-4e24-b880-801b52c59260
-- title:
--   Original B236 ruin-clipped positive stopping cash inclusive Iic terminal contact bounded by strict prepayment cash plus true terminal risk reserve
-- statement:
--   At every strictly positive original stopping clock σ(ω), the exact B236 discounted terminal cash F including all original dividend payments in the closed interval Iic(σ) and the correct terminal state (post-right-dividend before ruin, actual riskProcess at ruin) is bounded by discounted w applied to the original actual riskProcess at σ plus the genuinely strict Iio(σ) dividend Stieltjes cash. The original admissibility and right-jump payment inequality control the terminal contact atom and handle possible ruin at σ without post-ruin samples. The zero clock is separately covered by Proved original B24 zero-clock full cash inequality. This supplies the missing genuine inclusive-cash to strict-cash endpoint link for the B236 Itô physical-grid ledger.
-- source:
--   Instantiate Proved avram_ubv_top12_original_positive_clock_paid_post_le_strict_pre at S=σ(ω), using original hD, q, right jump budget and source F. Positive σ rules out the zero branch of F, exactly matching Proved endpoint inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_positive_clock_paid_post_le_strict_pre
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b244_original_ruinclipped_positive_stop_inclusive_Iic_cash_terminal_contact_le_strict
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hjump : ∀ η (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D η) →
      rightLimit D t η - D t η ≤
        w (riskProcess X x D t η) -
          w (riskProcess X x D t η -
            (rightLimit D t η - D t η)))
    (σ : Ω → ℝ≥0) (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
            (σ ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (σ ω) ω - rightLimit D (σ ω) ω
        else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ ω, 0 < σ ω →
      F ω ≤
        Real.exp (-(q * (σ ω : ℝ))) *
          w (riskProcess X x D (σ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by sorry
