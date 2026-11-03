-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_discounted_HJB_rightpayment_atom_bound
-- name    : AvramDividend.Classical.avram_chat07b_original_discounted_HJB_rightpayment_atom_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:49:53.860124+00:00
-- url     : https://prove2.me/theorems/3ee30c05-58db-4b24-bebd-f7683f15a91b
-- title:
--   Original discounted right-payment singleton is bounded by its physical HJB value drop
-- statement:
--   On the original SpectrallyNegativeLevy sample space, the actual discounted Stieltjes singleton atom at every pre-ruin or time-zero payment is at most the discounted ENNReal value drop under the canonical real lump-sum HJB jump inequality. It preserves the payment atom at zero and simultaneous source and dividend jumps; no source compensation or total payout bound is postulated.
-- source:
--   Avram Proposition 4(i): original physical dividendMeasure singleton identity 4f229f9a and core positive-cap lump-sum jump premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_chat07b_original_discounted_HJB_rightpayment_atom_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ (ω : Ω) (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) *
      dividendMeasure D ω {(t : ℝ)} ≤
    ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) *
      ENNReal.ofReal
        (w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) := by sorry
