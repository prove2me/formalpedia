-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_barrierSupValue_eq_sampled_cantor_expectation
-- name    : AvramDividend.Classical.avram_root29_05_barrierSupValue_eq_sampled_cantor_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:19:20.069347+00:00
-- url     : https://prove2.me/theorems/caf87735-37b4-4d69-97dc-2e7846281b0d
-- title:
--   Canonical at-barrier Stieltjes dividend value equals expected measurable Cantor-sampled path reward
-- statement:
--   For the original spectrally negative Lévy process and q≥0, the true expected discounted barrier running-supremum Stieltjes dividend reward, killed at canonical barrierRuinTime, is exactly the expectation of the globally measurable countably sampled record-dividend functional of the original full path. Uses the true original regulator dividend measure and strict drawdown ruin clock. This gives the source-level at-barrier expectation interface for killed-history strong-Markov first-upcrossing valuation, without assuming a scale-function identity.
-- source:
--   Canonically Proved original nonpositive payment-time nullity 280346b8, original strict drawdown clock 75280f18, and full pathwise original Stieltjes-to-sampled equality 43b6f24e.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_original_runningSup_stopped_reward_ignores_nonpositive_times
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_original_reflected_stieltjes_eq_sampled_cantor_reward

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- The genuine reflected-supremum dividend value is the expectation of
the globally measurable stopped Cantor-record reward of the original path. -/

theorem AvramDividend.Classical.avram_root29_05_barrierSupValue_eq_sampled_cantor_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a q : ℝ) (hq : 0 ≤ q) :
    barrierSupValue X a q =
      ∫⁻ ω : Ω,
        (let samples : ℕ → ℝ≥0 := fun j =>
           ((Nat.unpair j).2 : ℝ≥0) *
             (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
         let record : ℝ≥0 → ℝ := fun t =>
           (⨆ j : ℕ,
             if samples j ≤ t then
               ENNReal.ofReal (X.X (samples j) ω - X.X 0 ω) else 0).toReal
         let grid : ℕ → ℕ → ℝ≥0 := fun n k =>
           (k : ℝ≥0) * (((n + 1 : ℕ) : ℝ≥0)⁻¹)
         let ρ : ℝ≥0∞ := ⨅ i : ℕ,
           if X.X (samples i) ω - X.X 0 ω - record (samples i) < -a
           then (samples i : ℝ≥0∞) else ⊤
         ⨆ n : ℕ, ⨆ N : ℕ,
           ∑ k ∈ Finset.range N,
             if (grid n (k + 1) : ℝ≥0∞) < ρ then
               ENNReal.ofReal
                 (Real.exp (-(q * ((grid n (k + 1) : ℝ≥0) : ℝ)))) *
               ENNReal.ofReal
                 (record (grid n (k + 1)) - record (grid n k))
             else 0) ∂P := by sorry
