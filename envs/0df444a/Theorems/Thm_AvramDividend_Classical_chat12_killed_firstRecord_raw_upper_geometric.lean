-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_killed_firstRecord_raw_upper_geometric
-- name    : AvramDividend.Classical.chat12_killed_firstRecord_raw_upper_geometric
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:35:20.922635+00:00
-- url     : https://prove2.me/theorems/adc3afc3-e008-4a94-b77f-1143e6f89074
-- title:
--   Global raw two-sided-exit geometric upper budget for killed records
-- statement:
--   The Proved strong-Markov upper one-cycle expected record inequality implies that for each n≥0 the n-th killed upward record reward has expected discounted value at most the n-th power of the genuine discounted strict upper-before-lower exit expectation times the expected zero-th killed record reward. This is a scale-free geometric upper bound with no scale-function or q-scale exit identity prerequisites.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_next_expected_le_current_mul_twoSided

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_killed_firstRecord_raw_upper_geometric
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) :
    ∀ n : ℕ,
      (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P) ≤
      (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ^ n * (∫⁻ ω, if twoSidedExitUpTime X ((0 : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((0 : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by sorry
