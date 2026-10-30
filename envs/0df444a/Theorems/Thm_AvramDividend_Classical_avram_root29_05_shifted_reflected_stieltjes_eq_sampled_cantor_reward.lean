-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_reflected_stieltjes_eq_sampled_cantor_reward
-- name    : AvramDividend.Classical.avram_root29_05_shifted_reflected_stieltjes_eq_sampled_cantor_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:17:18.875688+00:00
-- url     : https://prove2.me/theorems/3c6aa6e6-1607-4639-aee9-eb1e4aaaef7b
-- title:
--   Genuine shifted killed future Stieltjes dividend equals measurable Cantor reward
-- statement:
--   For every actual Lévy path, finite shift and nonnegative discount, its true future shifted supremum Stieltjes payout stopped at strict reflected drawdown ruin agrees pathwise with the globally measurable countably sampled Cantor rational-record killed reward used in the independently proved first-upcrossing strong Markov factor.
-- source:
--   Combine Proved true shifted Stieltjes cash-grid supremum equality, shifted strict drawdown ruin clock equals sampled clock, dense-sampled future record equals the genuine shifted running supremum at all sampled and cash-grid endpoints. The theorem is a true shifted pathwise identity and makes no invalid shifted-law assumption.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_stieltjes_eq_killed_record_grid_sup
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_strict_drawdown_clock_eq_cantor_schedule
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_cantor_shifted_record_eq_true_shifted_sup_on_grid
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_shifted_levy_dense_prefix_eq_shiftedSup
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- Actual strictly killed future Lévy regulator Stieltjes cash matches
the same globally measurable Cantor-sampled future-path reward. -/

theorem AvramDividend.Classical.avram_root29_05_shifted_reflected_stieltjes_eq_sampled_cantor_reward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (age : ℝ≥0) (a q : ℝ) (hq : 0 ≤ q) :
    (let f : ℝ≥0 → ℝ := fun t => X.X (age + t) ω - X.X age ω
     let M : ℝ≥0 → ℝ := fun t => sSup (f '' Set.Icc 0 t)
     let τ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // f t - M t < -a},
       (i.1 : ℝ≥0∞)
     ∫⁻ r in paymentTimes τ,
       if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0
         ∂(dividendMeasure (fun t (_ : Ω) => M t) ω)) =
    (let f : ℝ≥0 → ℝ := fun t => X.X (age + t) ω - X.X age ω
     let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     let record : ℝ≥0 → ℝ := fun t =>
       (⨆ j : ℕ,
         if samples j ≤ t then
           ENNReal.ofReal (f (samples j) - f 0) else 0).toReal
     let grid : ℕ → ℕ → ℝ≥0 := fun n k =>
       (k : ℝ≥0) * (((n + 1 : ℕ) : ℝ≥0)⁻¹)
     let ρ : ℝ≥0∞ := ⨅ i : ℕ,
       if f (samples i) - f 0 - record (samples i) < -a
       then (samples i : ℝ≥0∞) else ⊤
     ⨆ n : ℕ, ⨆ N : ℕ,
       ∑ k ∈ Finset.range N,
         if (grid n (k + 1) : ℝ≥0∞) < ρ then
           ENNReal.ofReal
             (Real.exp (-(q * ((grid n (k + 1) : ℝ≥0) : ℝ)))) *
           ENNReal.ofReal
             (record (grid n (k + 1)) - record (grid n k))
         else 0) := by sorry
