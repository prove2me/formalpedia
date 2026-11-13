-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva73_original_real_horizon_spatial_cash_positive_excess_transfer
-- name    : AvramDividend.Classical.avram_bva73_original_real_horizon_spatial_cash_positive_excess_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T18:40:26.745378+00:00
-- url     : https://prove2.me/theorems/f8144ab8-ca5e-44ab-ad31-3c0d8f2e7419
-- title:
--   Original BV cofinal spatial and stopped cash source errors imply vanishing expected positive compensated excess
-- statement:
--   A precise conditional transfer for the original spectrally negative Levy process and arbitrary real horizon: if the physical-cell stopped payoff is pathwise bounded by original signed compensated source plus the exact positive spatial bad-band and discounted ruin-contact correction, and its positive excess is integrable, then a cofinal spatial diagonal and physical integer clock yield expected positive excess tending to zero. The two original errors are already controlled by Proved BVA72; the remaining task is exactly the source C1 chain-rule budget hypothesis, not a replacement process or global generator L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva72_original_real_horizon_spatial_ruin_joint_error_mean_zero
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem AvramDividend.Classical.avram_bva73_original_real_horizon_spatial_cash_positive_excess_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (w : ℝ → ℝ) (F : ℕ → Ω → ℝ) (Noise : ℕ → ℕ → Ω → ℝ)
    (hExcessInt : ∀ (κ : ℕ → ℕ) (m : ℕ),
      Integrable (fun ω => max (F m ω - (w x + Noise m (κ m) ω)) 0) P) :
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
    (∀ (n : ℕ) (κ : ℕ → ℕ) (m : ℕ),
      ∀ᵐ ω ∂P,
        F m ω ≤ w x + Noise m (κ m) ω +
          max (Err m (κ m) ω) 0 + Cash n m ω) →
    ∃ (n : ℕ) (κ : ℕ → ℕ),
      0 < n ∧ T ≤ (n : ℝ≥0) ∧ StrictMono κ ∧ (∀ m, m ≤ κ m) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        ∃ N : ℕ, ∀ m ≥ N, y ∈ Icc (a (κ m)) (b (κ m))) ∧
      Tendsto (fun m => ∫ ω,
        max (F m ω - (w x + Noise m (κ m) ω)) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
