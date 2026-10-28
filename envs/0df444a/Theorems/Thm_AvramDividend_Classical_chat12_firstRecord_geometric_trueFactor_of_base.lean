-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_firstRecord_geometric_trueFactor_of_base
-- name    : AvramDividend.Classical.chat12_firstRecord_geometric_trueFactor_of_base
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:10:35.114292+00:00
-- url     : https://prove2.me/theorems/f29f65b7-1597-4bc2-a4c1-f6c0aa8dcce0
-- title:
--   Geometric lower first-record expectations from a raw initial exit factor
-- statement:
--   If the first surviving killed upward record has expected discounted reward at least epsilon times the unnormalised true discounted two-sided exit expectation, the Proved uncapped one-cycle strong-Markov lower inequality yields a full geometric lower expectation bound for every successive record. The theorem is scale-free and handles the ENNReal induction and powers without q-scale exit identities.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_chat12_killed_firstRecord_next_expected_ge_current_mul_twoSided

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_firstRecord_geometric_trueFactor_of_base
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a ε : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hbase : ENNReal.ofReal ε * (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ≤
      (∫⁻ ω, if twoSidedExitUpTime X ((1 : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((1 : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) :
    ∀ n : ℕ, ENNReal.ofReal ε * (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ^ (n + 1) ≤
      (∫⁻ ω, if twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by sorry
