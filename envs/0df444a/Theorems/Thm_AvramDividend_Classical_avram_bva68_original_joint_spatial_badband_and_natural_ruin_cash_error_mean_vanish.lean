-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva68_original_joint_spatial_badband_and_natural_ruin_cash_error_mean_vanish
-- name    : AvramDividend.Classical.avram_bva68_original_joint_spatial_badband_and_natural_ruin_cash_error_mean_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:16:28.321202+00:00
-- url     : https://prove2.me/theorems/0d0ea55e-e4aa-4bb9-b529-27d84b1219f1
-- title:
--   Original BV joint spatial localisation and natural stopped cash errors have integrable vanishing positive mean
-- statement:
--   With the original spectrally negative Levy process and original admissible dividend strategy at positive integer horizon, one can select a cofinal interior spatial localisation diagonal so the sum of its positive bad-band physical variation error and the literal discounted strict ruin-clipped cash/mesh contact correction is integrable at each physical row and has expectation tending to zero. The same row index is used for both terms; neither global generator L1, finite activity nor independent replacement process is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva65_original_BV_diagonal_spatial_band_remains_cofinal
import Theorems.Thm_AvramDividend_Classical_avram_bva67_original_natural_ruin_clipped_cash_mesh_error_mean_zero
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva68_original_joint_spatial_badband_and_natural_ruin_cash_error_mean_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) (r : ℕ) (hr : 0 < r)
    (u : ℕ → ℕ → ℝ≥0) (a b : ℕ → ℝ)
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
          else |X.drift| * (r : ℝ) +
            |(r : ℝ) * X.drift - X.X (r : ℝ≥0) ω|
    let ρ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (r : ℝ≥0∞)).toNNReal
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ := (r : ℝ) / ((m : ℝ) + 2)
      let F : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      let T : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo ((ρ ω : ℝ) - Δ) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      q * Δ * Real.exp (q * (r : ℝ)) * F + T
    ∃ κ : ℕ → ℕ,
      StrictMono κ ∧ (∀ m, m ≤ κ m) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        ∃ N : ℕ, ∀ m ≥ N, y ∈ Icc (a (κ m)) (b (κ m))) ∧
      (∀ m, Integrable (fun ω => max (Err m (κ m) ω) 0 + E m ω) P) ∧
      Tendsto (fun m => ∫ ω, max (Err m (κ m) ω) 0 + E m ω ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
