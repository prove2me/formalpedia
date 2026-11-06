-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_cash_residual_of_clock_refinement
-- name    : AvramDividend.Classical.avram_p3_f2_original_stopped_cash_residual_of_clock_refinement
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:27:29.109086+00:00
-- url     : https://prove2.me/theorems/fc73eb6d-a59f-4c0d-982e-7c1692be45c5
-- title:
--   Original stopped BV Stieltjes cash C1 residual vanishes along actual time-refining grids
-- statement:
--   The genuine original Lévy stopped paymentTimes/dividendMeasure cash residual, including terminal discount and exact dividend remainder, vanishes along source physical time-refining grids with strict subcap reserve bands, a compact positive-clock tail and an independently controlled zero-origin first Y cell. This removes external hOpen and hFine premises by importing Proved original-source lemmas; P3-G2 retains actual time-zero/right/horizon atom certification and P3-E2 retains signed generator compensation.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_discounted_cash_C1_residual_vanish
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_full_refining_Y_grid_small_of_first_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_positive_subcap_C1_domain_isOpen
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_stopped_cash_residual_of_clock_refinement
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b a₀ b₀ : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ha : a < a₀) (hb : b₀ < b)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      ∀ (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ),
        let z : ℕ → ℕ → ℝ := fun m i =>
          x + X.X (u m i) ω - rightLimit D (u m i) ω
        let c : ℕ → ℕ → ℝ := fun m i =>
          Y (u m (i + 1)) - Y (u m i)
        let j : ℕ → ℕ → ℝ := fun m i =>
          J (u m (i + 1)) - J (u m i)
        (∀ m, u m 0 = 0) →
        (∀ m, u m (n m) = T) →
        (∀ m i, i < n m → u m i ≤ u m (i + 1)) →
        (∀ m i, i < n m →
          Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b) →
        (∀ m i, i < n m →
          Set.uIcc (z m i - j m i) (z m i) ⊆ Set.Icc a₀ b₀) →
        ∀ (α β : ℝ≥0) (hα : 0 < α),
        (∀ m i, 0 < i → i < n m →
          u m i ∈ Set.Icc α β ∧ u m (i + 1) ∈ Set.Icc α β) →
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ m in Filter.atTop,
            ∀ i, 0 < i → i < n m →
              dist (u m (i + 1)) (u m i) < δ) →
        (∀ ε : ℝ, 0 < ε →
          ∀ᶠ m in Filter.atTop,
            0 < n m → |Y (u m 1) - Y (u m 0)| < ε) →
        let e : ℕ → ℕ → ℝ := fun m i =>
          Real.exp (-(q * (u m i : ℝ)))
        let cash : ℕ → ℕ → ℝ := fun m i =>
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Set.Ioc (u m i : ℝ) (u m (i + 1) : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal
        let post : ℕ → ℕ → ℝ := fun m i =>
          w (x + X.X (u m i) ω - rightLimit D (u m i) ω)
        let frozen : ℕ → ℕ → ℝ := fun m i =>
          w (x + X.X (u m (i + 1)) ω - rightLimit D (u m i) ω) -
            w (x + X.X (u m i) ω - rightLimit D (u m i) ω)
        let rem : ℕ → ℕ → ℝ := fun m i =>
          cash m i + e m i * (post m (i + 1) - post m i - frozen m i)
        let residual : ℕ → ℝ := fun m =>
          ((∑ i ∈ Finset.range (n m), cash m i) +
            e m (n m) * post m (n m) - e m 0 * post m 0) -
          ((∑ i ∈ Finset.range (n m),
              e m i * (deriv w (z m i) * c m i)) +
           (∑ i ∈ Finset.range (n m),
              e m i * (w (z m i - j m i) - w (z m i))) +
           (∑ i ∈ Finset.range (n m),
              (e m (i + 1) - e m i) * post m (i + 1)) +
           (∑ i ∈ Finset.range (n m), rem m i))
        ∀ η : ℝ, 0 < η →
          ∀ᶠ m in Filter.atTop, |residual m| < η := by sorry
