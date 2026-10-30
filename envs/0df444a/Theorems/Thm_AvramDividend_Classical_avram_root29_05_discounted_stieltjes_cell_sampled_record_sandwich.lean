-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_discounted_stieltjes_cell_sampled_record_sandwich
-- name    : AvramDividend.Classical.avram_root29_05_discounted_stieltjes_cell_sampled_record_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:59:49.071983+00:00
-- url     : https://prove2.me/theorems/78cc0843-30f5-4d55-b4d4-d3f865abf637
-- title:
--   Genuine discounted Stieltjes cell payout sandwiched by Cantor sampled Lévy record increments
-- statement:
--   For each positive-denominator rational time cell and nonnegative discount rate, the true Stieltjes dividend paid by the reflected running-supremum regulator, weighted by exponential discount, lies between its end-of-cell and start-of-cell discount factors multiplied by the exactly sampled record increment. This pathwise two-sided estimate is the finite-cell analytic interface for passing the measurable killed rational-grid reward to the actual regulator payout.
-- source:
--   Uses Proved runningSup_discounted_interval_bounds_rightLim, runningSup_realTime_rightLim_eq and runningSup_eq_cantorSchedule_rationalGrid; no assumed exit or scale formula. Intermediate for genuine sampled-to-Stieltjes reward convergence under 79978d61.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_bounds_rightLim
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_rightLim_eq
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_cantorSchedule_rationalGrid

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_root29_05_discounted_stieltjes_cell_sampled_record_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (n k : ℕ) (hn : 0 < n) :
    let t : ℕ → ℝ≥0 := fun j => (j : ℝ≥0) * (n : ℝ≥0)⁻¹
    let sampledRecord : ℕ → ℝ := fun j =>
      ⨆ s : {s : ℝ≥0 //
        s ∈ Set.range (fun i : ℕ =>
          ((Nat.unpair i).2 : ℝ≥0) *
            (((((Nat.unpair i).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ∧ s ≤ t j},
        X.X s.1 ω
    let cash : ℝ≥0∞ :=
      ∫⁻ r, if r ∈ Set.Ioc (t k : ℝ) (t (k + 1) : ℝ)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)
    ENNReal.ofReal (Real.exp (-(q * (t (k + 1) : ℝ)))) *
        ENNReal.ofReal (sampledRecord (k + 1) - sampledRecord k) ≤ cash ∧
      cash ≤ ENNReal.ofReal (Real.exp (-(q * (t k : ℝ)))) *
        ENNReal.ofReal (sampledRecord (k + 1) - sampledRecord k) := by sorry
