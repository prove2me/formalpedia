-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict11_uniform_B_source_to_strict_expected_upper
-- name    : AvramDividend.Classical.avram_bv_strict11_uniform_B_source_to_strict_expected_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:01:32.040205+00:00
-- url     : https://prove2.me/theorems/3c70ab2c-b02d-4e49-899a-8934c720b990
-- title:
--   Actual original uniform-grid two-scale source entails full BV strict stopped expected payoff bound
-- statement:
--   For the original spectrally negative Lévy process and admissible dividend strategy, the exact prescribed uniform-grid two-scale centred source certificate, with original signed generator B, implies the full-horizon strict expected cash plus survivor-value bound. The proof preserves the raw BV residual and boundary/contact contributions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict11_uniform_B_source_to_strict_expected_upper
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
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (B : ℕ → Ω → ℝ)
    (hB : ∀ n ω,
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
           else 0) * (R (u n i) - R (u n (i + 1)))))
    (hSource :
      let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
      let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
      let F : ℕ → Ω → ℝ := fun n ω =>
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0)
      ∃ (M ErrCell ErrContact : ℕ → ℕ → Ω → ℝ) (η : ℕ → ℝ),
        (∀ n, 0 < η n) ∧
        Tendsto η atTop (nhds (0 : ℝ)) ∧
        (∀ n k, Integrable (M n k) P ∧
          (∫ ω, M n k ω ∂P) = 0) ∧
        (∀ n k, Integrable (fun ω => max (ErrCell n k ω) 0) P) ∧
        (∀ n k, Integrable (fun ω => max (ErrContact n k ω) 0) P) ∧
        (∀ n k, ∀ᵐ ω ∂P,
          F n ω ≤ w x + (M n k ω + B n ω) +
            max (ErrCell n k ω) 0 + max (ErrContact n k ω) 0) ∧
        (∀ n (ε : ℝ), 0 < ε →
          ∃ k : ℕ,
            (∫ ω, max (ErrCell n k ω) 0 ∂P) +
              (∫ ω, max (ErrContact n k ω) 0 ∂P) ≤ η n + ε)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    (∫ ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by sorry
