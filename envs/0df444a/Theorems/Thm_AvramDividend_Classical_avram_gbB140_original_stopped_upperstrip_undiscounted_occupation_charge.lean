-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB140_original_stopped_upperstrip_undiscounted_occupation_charge
-- name    : AvramDividend.Classical.avram_gbB140_original_stopped_upperstrip_undiscounted_occupation_charge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T19:05:04.16561+00:00
-- url     : https://prove2.me/theorems/cecea733-e0dc-489a-a88b-3e6d43bfea6c
-- title:
--   Stopped upper-strip Gaussian source charge bounded by unweighted physical-grid occupation duration
-- statement:
--   The exact original stopped upper-strip spatial source surplus is bounded by max(c,0) times the unweighted physical-grid length of cells where the strict original stopping mask is active and both prepayment and postpayment reserves exceed b. Combine Proved B139 with the inequality exp(-q s_i)≤1 for nonnegative discount q and physical time s_i≥0. This directly identifies the physical-grid occupation-duration charge needed in the repaired positive-drift caplinear cash budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB139_original_stopped_upperstrip_positive_drift_finitegrid_sum_bound
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB140_original_stopped_upperstrip_undiscounted_occupation_charge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m : ℕ) (ρ : ℝ≥0) (hq : 0 ≤ q) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Y : ℕ → ℝ := fun i => x + X.X (s i) ω - rightLimit D (s i) ω
    let Z : ℕ → ℝ := fun i => x + X.X (s i + Δ) ω - rightLimit D (s i) ω
    let V : ℝ → ℝ := fun y => if y ≤ b then w y else w b + (y - b)
    let centred : ℕ → ℝ := fun i =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (s i : ℝ)))
    (Finset.range (m + 1)).sum (fun i =>
      if s i < ρ ∧ b < Y i ∧ b < Z i then
        e i * (V (Z i) - V (Y i) - centred i) else 0) ≤
    (Finset.range (m + 1)).sum (fun i =>
      if s i < ρ ∧ b < Y i ∧ b < Z i then
        (Δ : ℝ) * max X.c 0 else 0) := by sorry
