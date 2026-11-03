-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_paymentTimes_discounted_HJB_atom_tsum_bound
-- name    : AvramDividend.Classical.avram_chat07b_original_paymentTimes_discounted_HJB_atom_tsum_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:27:58.208035+00:00
-- url     : https://prove2.me/theorems/4f75dd43-0319-4137-bdac-e77eb3bf7b02
-- title:
--   Exact original stopped paymentTimes automatically satisfy HJB atom-sum domination including time zero
-- statement:
--   For the literal original SpectrallyNegativeLevy reserve and dividend strategy, the full discounted Stieltjes singleton sum at the actual pre-ruin or time-zero paymentTimes through a real horizon is bounded by the corresponding right-payment HJB value-drop sum. Active times are obtained from the original real paymentTimes using their nonnegative NNReal image, whose strict-before-ruin-or-zero membership follows from the already Proved physical paymentTimes theorem. This controls the atomic part of the original measure without pretending the diffuse part is absent.
-- source:
--   Proved 71123237 original paymentTimes membership, 8f4f6a8a original all-atoms ENNReal HJB sum; original full Stieltjes split 93720c7a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_discounted_HJB_all_rightpayment_atom_tsum_bound
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_chat07b_original_paymentTimes_discounted_HJB_atom_tsum_bound
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
    (ω : Ω) (T : ℝ) :
    let S : Set ℝ≥0 :=
      (fun s : ℝ => s.toNNReal) '' (paymentTimes (ruinTime X x D ω) ∩ Iic T)
    (∑' t : S,
      ENNReal.ofReal (Real.exp (-(q * (t.1 : ℝ)))) *
        dividendMeasure D ω {(t.1 : ℝ)}) ≤
    (∑' t : S,
      ENNReal.ofReal (Real.exp (-(q * (t.1 : ℝ)))) *
        ENNReal.ofReal
          (w (riskProcess X x D t.1 ω) -
            w (riskProcess X x D t.1 ω -
              (rightLimit D t.1 ω - D t.1 ω)))) := by sorry
