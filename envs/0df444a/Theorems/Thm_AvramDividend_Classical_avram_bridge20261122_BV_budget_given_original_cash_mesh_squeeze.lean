-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_BV_budget_given_original_cash_mesh_squeeze
-- name    : AvramDividend.Classical.avram_bridge20261122_BV_budget_given_original_cash_mesh_squeeze
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T21:09:04.887182+00:00
-- url     : https://prove2.me/theorems/a0b348fc-ba97-4e9c-90be-bc5a1d398c31
-- title:
--   Original BV stopped HJB budget given genuine stopped Stieltjes finite mesh squeeze
-- statement:
--   Original physical BV process, stopped dividend measure, and terminal. Assumes the exact two-sided stopped cash mesh inequality for every actual path and grid. The remaining proof must establish the genuine signed stopped generator/HJB budget and remove the mesh cutoff.
-- source:
--   Original BV target 9cd69d89 and remote-Proved cash squeeze 9d83166d (ten-theorem cash chain); retains every source hypothesis and conclusion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_bridge20261122_BV_budget_given_original_cash_mesh_squeeze
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) 
    (hSourceCashMesh : ∀ (ω : Ω) (m n : ℕ),
      let S : ℝ≥0 := ⟨T, hT⟩
          let τ : ℝ≥0 :=
            (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
          let u : ℕ → ℝ≥0 := fun j =>
            min (((min j (m + 1) : ℕ) : ℝ≥0) *
              (S / (m + 1))) τ
          (ENNReal.ofReal (rightLimit D 0 ω) +
            (∑ i ∈ Finset.range n,
              ENNReal.ofReal (Real.exp (-(q * (u (i + 1) : ℝ)))) *
                (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
                    Ioc (u i : ℝ) (u (i + 1) : ℝ),
                  (1 : ℝ≥0∞) ∂(dividendMeasure D ω))) ≤
            ENNReal.ofReal (rightLimit D 0 ω) +
            (∑ i ∈ Finset.range n,
              (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
                  Ioc (u i : ℝ) (u (i + 1) : ℝ),
                ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))) ∧
          (ENNReal.ofReal (rightLimit D 0 ω) +
            (∑ i ∈ Finset.range n,
              (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
                  Ioc (u i : ℝ) (u (i + 1) : ℝ),
                ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) ≤
            ENNReal.ofReal (rightLimit D 0 ω) +
            (∑ i ∈ Finset.range n,
              ENNReal.ofReal (Real.exp (-(q * (u i : ℝ)))) *
                (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
                    Ioc (u i : ℝ) (u (i + 1) : ℝ),
                  (1 : ℝ≥0∞) ∂(dividendMeasure D ω))))
    ) :
    let S : ℝ≥0 := ⟨T,hT⟩
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, Term ω ∂P) ≤ w x  := by sorry
