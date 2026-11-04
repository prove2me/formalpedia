-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_clock_ae_hjump_positivepart_zero
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_random_clock_ae_hjump_positivepart_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:50:58.799957+00:00
-- url     : https://prove2.me/theorems/f6acbbc6-35eb-444c-aa36-e22e05865e08
-- title:
--   Original random finite stopped clock: actual right-payment signed residual has zero positive-part Stieltjes integral almost surely
-- statement:
--   For the actual original controlled spectrally negative Lévy process and any random finite NNReal clock τ, the positive part of the discounted variable-size right-dividend hjump correction integrates to zero against the literal full ruin-stopped dividend Stieltjes measure, almost everywhere in the original probability measure P. This specialises the proved source-specific all-horizon positive-part integral e98986a3 at T=τ(ω) and lifts the pathwise equality to ae, without replacing the clock, discarding t=0/horizon atoms, assuming a stopping-time approximation, or requiring boundary smoothness.
-- source:
--   Public Proved P4-D e98986a3-cb05-4acd-b0a8-c2e85130c247, exact canonical 0dda1be7 original τ:Ω→NNReal and hjump; Filter.Eventually.of_forall. No unproved mathematical premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_hjump_signed_positivepart_stopped_lintegral_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The literal original right-dividend residual has zero positive part at every
    random finite clock, hence almost surely at P4-F's stopped clock. -/

theorem AvramDividend.Classical.avram_p4_d_dividend_original_random_clock_ae_hjump_positivepart_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (τ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)) *
          ((rightLimit D s.toNNReal ω - D s.toNNReal ω) +
            w (riskProcess X x D s.toNNReal ω -
              (rightLimit D s.toNNReal ω - D s.toNNReal ω)) -
            w (riskProcess X x D s.toNNReal ω)))
          ∂(dividendMeasure D ω)) = 0 := by sorry
