-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_positive_shift_actual_generator_time_recombination
-- name    : AvramDividend.Classical.avram_chat24_positive_shift_actual_generator_time_recombination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T23:14:03.404291+00:00
-- url     : https://prove2.me/theorems/269be26a-5616-4a58-ae4e-feb24dcd0568
-- title:
--   Actual original shifted reserve generator and compensator time integrals recombine
-- statement:
--   Source-faithful analytic child of c7bf36f0-f960-43ea-a5bb-3c2843a7adb3. Proves the genuine physical drift time integral equals minus the actual Levy-intensity compensator time integral plus the signed actual generator remainder. It must establish required pathwise integrability from original BV compact C1 bounds and generator integrability, and use the Proved physical generator representation. No integrability or recombination equation is added as a hypothesis. This is independent of the stopped cash chain inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_chat24_positive_shift_actual_generator_time_recombination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_genint : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y)
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hTop : C = ⊤) (δ : ℝ) (hδ : 0 < δ) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let a : ℝ := min δ 1 / 2
    let b : ℝ := x + δ + T * X.drift + 1
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => (x + δ) + X.X s p.2 - rightLimit D s p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) ∧
          Y p.1 ∈ Icc a b ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1)) else 0
    let μ : Measure ℝ≥0 :=
      (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    ∀ᵐ ω ∂P,
      (∫ t, if (t : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) ∧ Y (t, ω) ∈ Icc a b then
        Real.exp (-(q * (t : ℝ))) *
          (X.drift * deriv w (Y (t, ω)) - q * w (Y (t, ω))) else 0 ∂μ) =
      -(∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μ) +
      (∫ t, if (t : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) ∧ Y (t, ω) ∈ Icc a b then
        Real.exp (-(q * (t : ℝ))) *
          (X.generator w (Y (t, ω)) - q * w (Y (t, ω))) else 0 ∂μ) := by sorry
