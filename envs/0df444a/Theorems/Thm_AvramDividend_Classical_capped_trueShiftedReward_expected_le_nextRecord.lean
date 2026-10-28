-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_trueShiftedReward_expected_le_nextRecord
-- name    : AvramDividend.Classical.capped_trueShiftedReward_expected_le_nextRecord
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:27:02.501984+00:00
-- url     : https://prove2.me/theorems/0ee8271a-3267-404f-bf71-0873b5b563fd
-- title:
--   Capped shifted two-sided-exit reward expectation bounded by next killed record
-- statement:
--   For a capped first upward record before ruin, the expectation of the discounted reward from the actual shifted Lévy path, weighted by ε, is at most the expected killed next-record payment. This lifts the proved pathwise record inequality via the proved continuous-to-countable exit reward identity and monotonicity of the nonnegative integral.
-- source:
--   Proved killed_nextRecord_uncapped_ge_capped_shiftedReward and levy_shifted_trueTwoSided_reward_eq_schedule.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_uncapped_ge_capped_shiftedReward
import Theorems.Thm_AvramDividend_Classical_levy_shifted_trueTwoSided_reward_eq_schedule

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.capped_trueShiftedReward_expected_le_nextRecord
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (N : ℝ≥0) :
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
       let u : ℝ≥0 := (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
       ENNReal.ofReal ε *
         (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
           (let g : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
            let ρ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // ε < g t}, (i.1 : ℝ≥0∞)
            let σ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // g t < ε - a}, (i.1 : ℝ≥0∞)
            if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0))
      else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
       ENNReal.ofReal (ε * Real.exp
         (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
     else 0 ∂P) := by sorry
