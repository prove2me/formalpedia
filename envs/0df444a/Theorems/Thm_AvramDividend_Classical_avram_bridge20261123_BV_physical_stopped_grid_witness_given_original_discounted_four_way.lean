-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_BV_physical_stopped_grid_witness_given_original_discounted_four_way
-- name    : AvramDividend.Classical.avram_bridge20261123_BV_physical_stopped_grid_witness_given_original_discounted_four_way
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T12:53:17.302875+00:00
-- url     : https://prove2.me/theorems/fd78bcf8-a90c-42da-9a5d-17e91f282cd1
-- title:
--   Original BV stopped physical-cell budget conditional on proved original discounted reserve four-way identity
-- statement:
--   The original root-connected BV physically stopped finite-grid HJB error witness, conditional on the exact proved original discounted controlled-reserve increment identity with the drift, jump, compensated residual and right-dividend components. All stopped martingale, cash Stieltjes and error-integrability source obligations remain Open.
-- source:
--   Original root-connected parent 2bc848f9 and now public, owner-verified Proved physical discounted four-way identity 2a606877. No private imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_BV_physical_stopped_grid_witness_given_original_discounted_four_way
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (hDiscountedFourWay : ∀ (ω : Ω)
      (u : ℕ → ℝ≥0) (n : ℕ),
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) - J t
    let U : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    (∑ i ∈ Finset.range n,
      e i * (deriv w (U (u i)) * (U (u (i + 1)) - U (u i)))) =
      (∑ i ∈ Finset.range n,
        e i * (deriv w (U (u i)) *
          (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) -
      (∑ i ∈ Finset.range n,
        e i * (deriv w (U (u i)) * (R (u (i + 1)) - R (u i)))) -
      (∑ i ∈ Finset.range n,
        e i * (deriv w (U (u i)) * (J (u (i + 1)) - J (u i)))) -
      (∑ i ∈ Finset.range n,
        e i * (deriv w (U (u i)) *
          (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω))))
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    ∃ (u : ℕ → ℕ → ℝ≥0) (M B Err : ℕ → Ω → ℝ),
      (∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = T - δ n)) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n ω,
        let Z : ℕ → ℝ := fun i => Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
        B n ω =
          (∑ i ∈ Finset.range (n + 1),
            if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
                0 < Z i ∧ ENNReal.ofReal (Z i) < C then
              Real.exp (-(q * (u n i : ℝ))) *
                (X.generator w (Z i) - q * w (Z i)) *
                ((u n (i + 1) : ℝ) - (u n i : ℝ))
            else 0) +
          (let J : ℝ≥0 → ℝ := fun t =>
            ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
            else 0
           let R : ℝ≥0 → ℝ := fun t =>
            ((t : ℝ) * X.drift - X.X t ω) - J t
           ∑ i ∈ Finset.range (n + 1),
             (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
                 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
               Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
             else 0) * (R (u n i) - R (u n (i + 1))))) ∧
      (∀ n, Integrable (M n) P ∧
        (∫ ω, M n ω ∂P) = 0 ∧ Integrable (B n) P) ∧
      (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
      Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (𝓝 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0) ≤
        w x + (M n ω + B n ω) + max (Err n ω) 0) := by sorry
