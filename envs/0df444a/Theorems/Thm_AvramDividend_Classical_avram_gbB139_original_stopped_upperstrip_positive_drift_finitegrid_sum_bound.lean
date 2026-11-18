-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB139_original_stopped_upperstrip_positive_drift_finitegrid_sum_bound
-- name    : AvramDividend.Classical.avram_gbB139_original_stopped_upperstrip_positive_drift_finitegrid_sum_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:58:58.625432+00:00
-- url     : https://prove2.me/theorems/9110c5c2-5e36-4f3f-8d57-cd7776b87955
-- title:
--   Original stopped physical-grid upper-strip caplinear drift sum carries positive occupation charge
-- statement:
--   On the actual Gaussian Lévy physical grid, apply the source-faithful Proved B68 caplinear upper-strip increment inequality only to cells whose prepayment time is strictly before the original stopping horizon rho and whose prepayment/postpayment reserves both exceed b. The discounted stopped upper-strip spatial cash-minus-centred-noise surplus is bounded by max(X.c,0) times discounted physical time-width of exactly those stopped upper-strip cells. This gives the pathwise stopped positive-drift occupation correction required by the valid finite-cap cash route.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB68_original_upperstrip_discounted_physical_gaussian_source_drift_envelope
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB139_original_stopped_upperstrip_positive_drift_finitegrid_sum_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m : ℕ) (ρ : ℝ≥0) :
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
        e i * (Δ : ℝ) * max X.c 0 else 0) := by sorry
