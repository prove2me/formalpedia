-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva72_original_real_horizon_spatial_ruin_joint_error_mean_zero
-- name    : AvramDividend.Classical.avram_bva72_original_real_horizon_spatial_ruin_joint_error_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:47:53.135957+00:00
-- url     : https://prove2.me/theorems/bb50d22f-89ed-4b51-821b-a85847537513
-- title:
--   Original BV arbitrary real-horizon combined spatial and clipped cash errors vanish in expectation
-- statement:
--   For any finite nonnegative real horizon T, original standing BV spectrally negative Levy X, original admissible dividend strategy D, and cofinal interior bands, choose a fast cofinal spatial diagonal κ and an integer mesh bound n above T. Their combined positive spatial error and exact discounted natural ruin-clipped cash/contact error is integrable on every row and has expectation tending to zero. Does not add finite activity or global generator L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva65_original_BV_diagonal_spatial_band_remains_cofinal
import Theorems.Thm_AvramDividend_Classical_avram_bva71_original_arbitrary_real_horizon_clipped_ruin_cash_error_certificate
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem AvramDividend.Classical.avram_bva72_original_real_horizon_spatial_ruin_joint_error_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k)) :
    let Err : ℕ → ℕ → Ω → ℝ := fun n k ω =>
      if ∀ i < n + 1,
        (0 < Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i) ∧
          ENNReal.ofReal (Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)) < C) →
        Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)
            ∈ Icc (a k) (b k) then (0 : ℝ)
          else |X.drift| * (T : ℝ) +
            |(T : ℝ) * X.drift - X.X T ω|
    let ρ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let Cash : ℕ → ℕ → Ω → ℝ := fun n m ω =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
      let F : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      let T : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo ((ρ ω : ℝ) - Δ) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      q * Δ * Real.exp (q * (n : ℝ)) * F + T
    ∃ (n : ℕ) (κ : ℕ → ℕ),
      0 < n ∧ T ≤ (n : ℝ≥0) ∧ StrictMono κ ∧ (∀ m, m ≤ κ m) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        ∃ N : ℕ, ∀ m ≥ N, y ∈ Icc (a (κ m)) (b (κ m))) ∧
      (∀ m, Integrable (fun ω => max (Err m (κ m) ω) 0 + Cash n m ω) P) ∧
      Tendsto (fun m => ∫ ω, max (Err m (κ m) ω) 0 + Cash n m ω ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
