-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_dividendValue_eq_killed_cantor_expectation
-- name    : AvramDividend.Classical.avram_root29_05_dividendValue_eq_killed_cantor_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:38:15.729579+00:00
-- url     : https://prove2.me/theorems/5ff61019-349e-454f-8462-735afb4691ac
-- title:
--   Actual barrier dividend value as successful-upcrossing killed Cantor reward expectation
-- statement:
--   For the genuine source barrier strategy started below a positive cap, expected killed regulator Stieltjes dividends equal the strict first-upcrossing discounted expectation of the fully measurable Cantor-sampled future Lévy increment record reward.
-- source:
--   Use Proved original future-ruin stopped dividend identity d16ead6f, exact source raw-versus-controlled upcrossing event 374d2f8d, and the source-faithful raw future Stieltjes-to-Cantor pointwise bridge.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_dividendValue_barrierStrategy_expected_futureRuin_stoppedReward
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_upExit_before_controlledRuin_iff_rawExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_raw_future_stieltjes_eq_cantor
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- The original strategy's expected killed Stieltjes dividends are the
actual first-upcrossing-discounted countable future-record reward. -/

theorem AvramDividend.Classical.avram_root29_05_dividendValue_eq_killed_cantor_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x a : ℝ)
    (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) (hq : 0 ≤ q) :
    dividendValue X q x (barrierStrategy X x a) =
    (let T := twoSidedExitUpTime X (a - x)
     let R := ruinTime X x (barrierStrategy X x a)
     let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) * (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     let grid : ℕ → ℕ → ℝ≥0 := fun n k => (k : ℝ≥0) * (((n + 1 : ℕ) : ℝ≥0)⁻¹)
     ∫⁻ ω, if T ω < R ω then
       ENNReal.ofReal (Real.exp (-(q * ((T ω).toNNReal : ℝ)))) *
       (let f : ℝ≥0 → ℝ := fun t =>
          X.X ((T ω).toNNReal + t) ω - X.X ((T ω).toNNReal) ω
        let record : ℝ≥0 → ℝ := fun t =>
          (⨆ j : ℕ, if samples j ≤ t then ENNReal.ofReal (f (samples j) - f 0) else 0).toReal
        let ρ : ℝ≥0∞ := ⨅ i : ℕ, if f (samples i) - f 0 - record (samples i) < -a
          then (samples i : ℝ≥0∞) else ⊤
        ⨆ n : ℕ, ⨆ N : ℕ, ∑ k ∈ Finset.range N,
          if (grid n (k + 1) : ℝ≥0∞) < ρ then
            ENNReal.ofReal (Real.exp (-(q * ((grid n (k + 1) : ℝ≥0) : ℝ)))) *
            ENNReal.ofReal (record (grid n (k + 1)) - record (grid n k)) else 0)
     else 0 ∂P) := by sorry
