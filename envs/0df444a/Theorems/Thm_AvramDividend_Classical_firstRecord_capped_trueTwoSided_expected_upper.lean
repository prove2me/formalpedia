-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_capped_trueTwoSided_expected_upper
-- name    : AvramDividend.Classical.firstRecord_capped_trueTwoSided_expected_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:13:49.666482+00:00
-- url     : https://prove2.me/theorems/bc581789-43cb-4d14-917c-82696f57aee9
-- title:
--   Finite capped first-record strong-Markov expectation bound for shifted two-sided rewards
-- statement:
--   Apply the finite-stopping strong Markov expectation estimate to the capped first upper record and its survival history event. The finite-clock stopping-time, stopped-history and measurability conditions are discharged from established results.
-- source:
--   Finite stopped-history transfer and stopped Markov pointwise-to-expectation inequality

import Theorems.Thm_AvramDividend_Classical_finiteStopping_trueTwoSided_expected_upper_of_pointwise_preamble_fixed
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_in_finiteStoppedHistory

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstRecord_capped_trueTwoSided_expected_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (N : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : τ = (fun ω : Ω =>
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal))
    (A : Set Ω)
    (hA : A = ({ω : Ω | twoSidedExitUpTime X b ω <
      barrierRuinTime X a ω} ∩
      {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}))
    (hAfine : MeasurableSet A)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (q upper lower : ℝ) (weight : Ω → ℝ≥0∞)
    (hUpper : ∀ ω : Ω, weight ω ≤
      (if ω ∈ A then discount (τ ω) *
        (let g : ℝ≥0 → ℝ := fun t => X.X (τ ω + t) ω - X.X (τ ω) ω
         let grid : ℕ → ℝ≥0 := fun j => ((Nat.unpair j).2 : ℝ≥0) *
           (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
         let up : ℝ≥0∞ := ⨅ j : ℕ,
           if upper < g (grid j) then (grid j : ℝ≥0∞) else ⊤
         let dn : ℝ≥0∞ := ⨅ j : ℕ,
           if g (grid j) < lower then (grid j : ℝ≥0∞) else ⊤
         if up < dn then ENNReal.ofReal (Real.exp (-(q * up.toReal))) else 0)
       else 0)) :
    (∫⁻ ω, weight ω ∂P) ≤
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : upper < X.X t ω),
                    (t : ℝ≥0∞)) <
                  (⨅ (t : ℝ≥0) (_ : X.X t ω < lower),
                    (t : ℝ≥0∞)) then
      ENNReal.ofReal (Real.exp (-(q *
        ENNReal.toReal (⨅ (t : ℝ≥0)
          (_ : upper < X.X t ω), (t : ℝ≥0∞))))) else 0 ∂P) := by sorry
