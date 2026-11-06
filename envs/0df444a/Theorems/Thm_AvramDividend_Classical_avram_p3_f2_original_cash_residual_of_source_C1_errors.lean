-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_cash_residual_of_source_C1_errors
-- name    : AvramDividend.Classical.avram_p3_f2_original_cash_residual_of_source_C1_errors
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:05:45.6192+00:00
-- url     : https://prove2.me/theorems/d3dc4ed8-9925-41b1-8b00-1592796d0f2a
-- title:
--   Original stopped paymentTimes cash residual follows physical C1 grid-error convergence
-- statement:
--   For the actual spectrally negative Lévy process X and original dividend measure D, the exact finite-grid cash/Y/J/discount identity implies eventual smallness of the stopped cash residual as soon as the two physical C1 error sums vanish along the specified grids. This is a source-specific conditional analytic interface: no mean-zero, expectation, or fictitious dividend process is used.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_full_cash_Y_J_C1_commutator_identity
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_cash_residual_of_source_C1_errors
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
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
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ m in Filter.atTop, ∀ i, i < n m → |c m i| < δ) →
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
        (∀ η : ℝ, 0 < η →
          ∀ᶠ m in Filter.atTop, |(∑ i ∈ Finset.range (n m),
              Real.exp (-q * (u m i : ℝ)) *
                (w (z m i + c m i - j m i) - w (z m i + c m i) -
                  w (z m i - j m i) + w (z m i))) + (∑ i ∈ Finset.range (n m),
              Real.exp (-q * (u m i : ℝ)) *
                (w (z m i + c m i) - w (z m i) -
                  deriv w (z m i) * c m i))| < η) →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ m in Filter.atTop, |residual m| < η := by sorry
