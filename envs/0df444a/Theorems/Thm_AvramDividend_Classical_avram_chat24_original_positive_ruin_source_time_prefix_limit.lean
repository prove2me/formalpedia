-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_original_positive_ruin_source_time_prefix_limit
-- name    : AvramDividend.Classical.avram_chat24_original_positive_ruin_source_time_prefix_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:26:38.256229+00:00
-- url     : https://prove2.me/theorems/a66ab8c0-3d45-4f84-929c-887f7c30edf0
-- title:
--   Original source/time prefix limit differs from the stopped value by the final actual source atom
-- statement:
--   Source-faithful child of 241a8ec2-a2bd-474c-bee2-6824b1376722. Dominated convergence under the actual mapped jump measure gives the strict source prefix; absolute original-jump summability and the compact analytic bound dominate its kernel. The physical-time measure is finite and atomless at the endpoint, so its bounded integrand converges to the stopped integral. The only difference from the stopped source is the exact actual atom J at positive ruin. No pure-jump drift identity or source/time grid equality is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_chat24_original_positive_ruin_source_time_prefix_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
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
    let K : Ω → ℝ≥0 → ℝ := fun ω B =>
      (∫⁻ t in Ico (0 : ℝ) (B : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let V : Ω → ℝ≥0 → ℝ := fun ω B =>
      Real.exp (-(q * (B : ℝ))) * w (riskProcess X x D B ω + δ)
    let R : Ω → ℝ≥0 → ℝ := fun ω B =>
      (∫ p, if (p.1 : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧
          Y (p.1, ω) ∈ Icc a b ∧ p.2 < 0 then
        Real.exp (-(q * (p.1 : ℝ))) *
          (w (Y (p.1, ω) + p.2) - w (Y (p.1, ω))) else 0 ∂(NX ω)) +
      (∫ t, if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y (t, ω) ∈ Icc a b then
        Real.exp (-(q * (t : ℝ))) *
          (X.drift * deriv w (Y (t, ω)) - q * w (Y (t, ω))) else 0 ∂μ)
    let Kstop : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let J : Ω → ℝ := fun ω =>
      let z : ℝ := X.X (τ ω) ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) (τ ω)
      if Y (τ ω, ω) ∈ Icc a b ∧ z < 0 then
        Real.exp (-(q * (τ ω : ℝ))) * (w (Y (τ ω, ω) + z) - w (Y (τ ω, ω))) else 0
    ∀ᵐ ω ∂P, 0 < ruinTime X x D ω →
      ruinTime X x D ω ≤ (S : ℝ≥0∞) →
      ∀ u : ℕ → ℝ≥0,
        (∀ n, 0 < u n ∧ u n ≤ S ∧ (u n : ℝ≥0∞) < ruinTime X x D ω) →
        Monotone u → Tendsto u atTop (nhds (τ ω)) →
        Tendsto (fun n => R ω (u n)) atTop (nhds (R ω (τ ω) - J ω)) := by sorry
