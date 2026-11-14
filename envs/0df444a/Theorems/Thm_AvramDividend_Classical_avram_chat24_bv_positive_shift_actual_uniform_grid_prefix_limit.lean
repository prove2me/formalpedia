-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_bv_positive_shift_actual_uniform_grid_prefix_limit
-- name    : AvramDividend.Classical.avram_chat24_bv_positive_shift_actual_uniform_grid_prefix_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T23:57:50.007504+00:00
-- url     : https://prove2.me/theorems/8ee5bfc7-c7d8-44b0-904f-a68e4becd13f
-- title:
--   Actual uniform-grid BV source and cash limits give the original positive-shift prefix chain
-- statement:
--   Child of 290bbeb6-ae81-4ece-9a9d-91b8984cfc43. Given the exact explicit finite budgets, prove the real strict-prefix chain with actual intrinsic NX integral and physical time drift. The proof must establish actual strict cash convergence, source loss cell masses, proportional jump allocation and dominated tsum limit, and exact affine drift-segment integral convergence. The mesh is explicitly B/(n+1), which tends to zero; no arbitrary monotone-grid convergence is asserted. No convergence or integrability fact is inserted as a hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_chat24_bv_positive_shift_actual_uniform_grid_prefix_limit
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
    (∀ ω (B : ℝ≥0), 0 < B → B ≤ S →
      (B : ℝ≥0∞) < ruinTime X x D ω → ∀ n : ℕ,
    let N : ℕ := n + 1
    let u : ℕ → ℝ≥0 := fun i => B * (i : ℝ≥0) / (N : ℝ≥0)
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let U : ℕ → ℝ := fun i => riskProcess X x D (u i) ω + δ
    let Z : ℕ → ℝ := fun i => x + δ + X.X (u (i + 1)) ω - D (u i) ω
    (∑ i ∈ Finset.range N, e i * (D (u (i + 1)) ω - D (u i) ω)) + e N * w (U N) ≤
      w (x + δ) + (∑ i ∈ Finset.range N,
        ((e (i + 1) - e i) * w (U i) + e (i + 1) * (w (Z i) - w (U i)))) +
        q * ((B : ℝ) / (N : ℝ)) * D B ω) →
    ∀ᵐ ω ∂P, ∀ B : ℝ≥0, 0 < B → B ≤ S →
      (B : ℝ≥0∞) < ruinTime X x D ω →
      (∫⁻ t in Ico (0 : ℝ) (B : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        Real.exp (-(q * (B : ℝ))) * w (riskProcess X x D B ω + δ) ≤
      w (x + δ) +
        (∫ p, if (p.1 : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧
            Y (p.1, ω) ∈ Icc a b ∧ p.2 < 0 then
          Real.exp (-(q * (p.1 : ℝ))) *
            (w (Y (p.1, ω) + p.2) - w (Y (p.1, ω))) else 0 ∂(NX ω)) +
        (∫ t, if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y (t, ω) ∈ Icc a b then
          Real.exp (-(q * (t : ℝ))) *
            (X.drift * deriv w (Y (t, ω)) - q * w (Y (t, ω))) else 0 ∂μ) := by sorry
