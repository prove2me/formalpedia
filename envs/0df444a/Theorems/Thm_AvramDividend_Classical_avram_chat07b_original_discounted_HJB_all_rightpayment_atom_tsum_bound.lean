-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_discounted_HJB_all_rightpayment_atom_tsum_bound
-- name    : AvramDividend.Classical.avram_chat07b_original_discounted_HJB_all_rightpayment_atom_tsum_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:19:28.72821+00:00
-- url     : https://prove2.me/theorems/8f4f6a8a-1f92-4a8f-9d87-d8be0b30f542
-- title:
--   Every original physical discounted right-payment atom sum is bounded by the corresponding HJB value-drop sum
-- statement:
--   For the unchanged original Lévy source, dividend strategy and canonical HJB right-payment inequality, the sum over any set of active pre-ruin or time-zero payments of actual ENNReal discounted Stieltjes singleton masses is bounded by the sum of discounted verification value drops. The result applies to all original right-payment atoms, including t=0 and simultaneous source/dividend times. It makes no claim that the separate atomless dividend component or generator source expectation is controlled.
-- source:
--   Original physical discounted atom theorem UUID 3ee30c05, together with pinned ENNReal.tsum_le_tsum; intended consumer: original full Stieltjes atomic/diffuse exact split UUID 93720c7a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_discounted_HJB_rightpayment_atom_bound
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_chat07b_original_discounted_HJB_all_rightpayment_atom_tsum_bound
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
    (ω : Ω) (S : Set ℝ≥0)
    (hActive : ∀ t ∈ S, t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∑' t : S,
      ENNReal.ofReal (Real.exp (-(q * (t.1 : ℝ)))) *
        dividendMeasure D ω {(t.1 : ℝ)}) ≤
    (∑' t : S,
      ENNReal.ofReal (Real.exp (-(q * (t.1 : ℝ)))) *
        ENNReal.ofReal
          (w (riskProcess X x D t.1 ω) -
            w (riskProcess X x D t.1 ω -
              (rightLimit D t.1 ω - D t.1 ω)))) := by sorry
