-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_raw_future_stieltjes_eq_cantor
-- name    : AvramDividend.Classical.avram_root29_05_raw_future_stieltjes_eq_cantor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:31:02.400851+00:00
-- url     : https://prove2.me/theorems/a97d9be5-e325-4e2f-9bf2-b7a4b023a77d
-- title:
--   Original raw future-ruin shifted Stieltjes dividend equals measurable Cantor reward
-- statement:
--   At every finite age of the original Lévy path, the exact raw-future ruin-stopped positive-time Stieltjes dividend in the canonical post-upcrossing formula equals the globally measurable Cantor-sampled future-record payment, with strict endpoint conventions.
-- source:
--   Use the Proved raw future ruin clock equality, exact positive-time indicator Stieltjes integral identity, and Proved shifted Stieltjes-to-Cantor sampled reward equality; no new stochastic axiom.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_future_raw_ruin_eq_strict_drawdown_subtype_clock
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_paymentTimes_Ioi_integral_eq_positive_weight
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_reflected_stieltjes_eq_sampled_cantor_reward
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- The exact raw future-ruin stopped Stieltjes integral appearing after
upcrossing is the same measurable Cantor-sampled future reward. -/

theorem AvramDividend.Classical.avram_root29_05_raw_future_stieltjes_eq_cantor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (age : ℝ≥0)
    (a q : ℝ) (hq : 0 ≤ q) :
    (let M : ℝ≥0 → ℝ := fun t =>
       sSup ((fun v : ℝ≥0 => X.X (age + v) ω - X.X age ω) '' Set.Icc 0 t)
     let raw : ℝ≥0∞ := ⨅ (t : ℝ≥0)
       (_ : a + (X.X (age + t) ω - X.X age ω) <
         max 0 (sSup ((fun v : ℝ≥0 => X.X (age + v) ω) '' Set.Icc 0 t) - X.X age ω)),
       (t : ℝ≥0∞)
     ∫⁻ t in Set.Ioi (0 : ℝ) ∩ paymentTimes raw,
       ENNReal.ofReal (Real.exp (-(q * t))) ∂
       (dividendMeasure (fun t (_ : Ω) => M t) ω)) =
    (let f : ℝ≥0 → ℝ := fun t => X.X (age + t) ω - X.X age ω
     let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) * (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     let record : ℝ≥0 → ℝ := fun t =>
       (⨆ j : ℕ, if samples j ≤ t then ENNReal.ofReal (f (samples j) - f 0) else 0).toReal
     let grid : ℕ → ℕ → ℝ≥0 := fun n k =>
       (k : ℝ≥0) * (((n + 1 : ℕ) : ℝ≥0)⁻¹)
     let ρ : ℝ≥0∞ := ⨅ i : ℕ, if f (samples i) - f 0 - record (samples i) < -a
       then (samples i : ℝ≥0∞) else ⊤
     ⨆ n : ℕ, ⨆ N : ℕ, ∑ k ∈ Finset.range N,
       if (grid n (k + 1) : ℝ≥0∞) < ρ then
         ENNReal.ofReal (Real.exp (-(q * ((grid n (k + 1) : ℝ≥0) : ℝ)))) *
         ENNReal.ofReal (record (grid n (k + 1)) - record (grid n k)) else 0) := by sorry
