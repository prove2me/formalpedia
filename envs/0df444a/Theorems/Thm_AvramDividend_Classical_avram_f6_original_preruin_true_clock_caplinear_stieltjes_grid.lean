-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_preruin_true_clock_caplinear_stieltjes_grid
-- name    : AvramDividend.Classical.avram_f6_original_preruin_true_clock_caplinear_stieltjes_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:13:58.421182+00:00
-- url     : https://prove2.me/theorems/8f105a9a-f1d3-486a-a1af-13f300115204
-- title:
--   Original strictly pre-ruin stopping clock caplinear discounted Stieltjes cash grid
-- statement:
--   For the original spectrally negative Levy process and admissible capped strategy, a strictly pre-ruin real stopping clock automatically satisfies every pre-ruin physical grid cell condition; therefore the true original zero-time dividend-inclusive caplinear Stieltjes source ledger holds at that clock for any finite physical grid. All payout and time definitions are unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_preruin_true_clock_caplinear_stieltjes_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0) (n m : ℕ) (ω : Ω)
    (hσpre : (σ ω : ℝ≥0∞) < ruinTime X x D ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (v i : ℝ)))
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let Y : ℕ → ℝ := fun i =>
      x + X.X (v i) ω - rightLimit D (v i) ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in Ioc (v i : ℝ) (v (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
    let err : ℕ → ℝ := fun i =>
      (e i - e (i + 1)) * (V (Z i) - V (Y (i + 1)))
    (∫⁻ t in Icc (0 : ℝ) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal +
      e m * V (Y m) + (Finset.range m).sum cash ≤
      V x +
      (Finset.range m).sum (fun i =>
        e (i + 1) * V (Z i) - e i * V (Y i)) +
      (Finset.range m).sum err := by sorry
