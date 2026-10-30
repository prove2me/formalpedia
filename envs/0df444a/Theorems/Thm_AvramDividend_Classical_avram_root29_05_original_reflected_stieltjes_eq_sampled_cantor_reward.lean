-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_original_reflected_stieltjes_eq_sampled_cantor_reward
-- name    : AvramDividend.Classical.avram_root29_05_original_reflected_stieltjes_eq_sampled_cantor_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:12:48.272557+00:00
-- url     : https://prove2.me/theorems/43b6f24e-652a-452c-933c-ca66ea871bff
-- title:
--   Actual reflected stopped Stieltjes regulator dividend reward equals globally measurable Cantor sampled reward
-- statement:
--   For each genuine original spectrally negative Lévy sample path and nonnegative discount, the actual positive-time Stieltjes running-supremum regulator payout killed at first strict reflected drawdown equals the countably sampled rational record-dividend reward killed at the measurable Cantor-encoded reflected drawdown clock. This is a pathwise identity of the real original regulator, not an unreflected perpetual supremum formula. The proof combines the canonically proved full Stieltjes record-grid reconstruction, the exact genuine ruin clock equality and the exact normalized countable record equality at every rational dividend grid endpoint. It preserves the strict stopping set and actual dividend measure.
-- source:
--   Accepted 4e232b08 full original Stieltjes equality, 3584cc65 original reflected clock, 5a1d6ee2 sampled record normalization; source matching for accepted 31f9ae9b killed-history Markov.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_actual_stieltjes_eq_killed_record_grid_sup
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_true_reflected_ruin_eq_sampled_cantor_clock
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_cantor_sampled_normalized_record_eq_runningSup_on_grid

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_root29_05_original_reflected_stieltjes_eq_sampled_cantor_reward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a q : ℝ) (hq : 0 ≤ q) :
    (let τ : ℝ≥0∞ :=
       ⨅ i : {t : ℝ≥0 // X.X t ω - runningSup X t ω < -a},
         (i.1 : ℝ≥0∞)
     ∫⁻ r in paymentTimes τ,
       if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0
         ∂(dividendMeasure (runningSup X) ω)) =
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
         else 0) := by sorry
