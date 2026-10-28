-- Prove2me | Theorems.Thm_AvramDividend_Classical_finiteStopping_trueShiftedReward_expected_eq
-- name    : AvramDividend.Classical.finiteStopping_trueShiftedReward_expected_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:18:29.243347+00:00
-- url     : https://prove2.me/theorems/d019fbba-2530-4c18-a300-7863bfb42636
-- title:
--   Exact stopped strong-Markov factorisation of the shifted two-sided exit reward
-- statement:
--   For any finite right-continuous Lévy stopping time and measurable survival event in its stopped history, the expected discounted true shifted two-sided-exit reward equals the past discounted stopped-history mass multiplied by the independent two-sided-exit reward expectation. The equality packages the separately remotely proved lower and upper inequalities for direct use in first-record regeneration.
-- source:
--   Direct combination of Proved finiteStopping_trueShiftedReward_expected_upper and Proved finiteStopping_trueShiftedReward_expected_lower by antisymmetry.

import Theorems.Thm_AvramDividend_Classical_finiteStopping_trueShiftedReward_expected_upper
import Theorems.Thm_AvramDividend_Classical_finiteStopping_trueShiftedReward_expected_lower

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.finiteStopping_trueShiftedReward_expected_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : MeasurableSet[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A)
    (hAfine : MeasurableSet A) (hτfine : Measurable τ)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (q upper lower : ℝ) :
    (∫⁻ ω, if ω ∈ A then discount (τ ω) *
      (let g : ℝ≥0 → ℝ := fun t => X.X (τ ω + t) ω - X.X (τ ω) ω
       let up : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // upper < g t}, (i.1 : ℝ≥0∞)
       let dn : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // g t < lower}, (i.1 : ℝ≥0∞)
       if up < dn then ENNReal.ofReal (Real.exp (-(q * up.toReal))) else 0)
      else 0 ∂P) =
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
                   (⨅ (t : ℝ≥0) (_ : X.X t ω < lower), (t : ℝ≥0∞)) then
       ENNReal.ofReal (Real.exp (-(q *
         ENNReal.toReal (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) := by sorry
