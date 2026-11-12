-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger128_original_positive_clock_fixed_mesh_cash_budget
-- name    : AvramDividend.Classical.avram_gledger128_original_positive_clock_fixed_mesh_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:21:55.285897+00:00
-- url     : https://prove2.me/theorems/525022ae-5d40-4af0-a6d2-11c4c03b340b
-- title:
--   Original positive-stop fixed clipped mesh dividend-contact budget
-- statement:
--   For one original sample path, one positive stopped clock strictly before ruin, and one deterministic clipped mesh, the genuine original Stieltjes cash and dividend-contact loss fit the positive mesh budget. The probabilistic almost-everywhere statement is reduced to its pathwise positive-stop source estimate.
-- source:
--   Original process X, original admissible D, exact paymentTimes and ruin cutoff. Derived from the Proved interior cash rate gledger112, first crossing gledger110, initial cash atom gledger117, terminal crossing gledger118 and finite real cash partition gledger108.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger128_original_positive_clock_fixed_mesh_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (n : ℕ) (ρ : ℝ≥0)
    (hρpos : 0 < ρ) (hρn : ρ ≤ (n : ℝ≥0))
    (hρruin : (ρ : ℝ≥0∞) ≤ ruinTime X x D ω)
    (j : ℕ)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1))
    (m : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℕ → ℝ := fun i =>
      x + X.X (v i) ω - rightLimit D (v i) ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let F : ℝ :=
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
    let B : ℝ :=
      let δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
      let T : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo ((ρ : ℝ) - δ) (ρ : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      q * δ * Real.exp (q * (n : ℝ)) * F + T
    max (
      (w (x - rightLimit D 0 ω) - w x) +
      Finset.sum (Finset.range (m + 2)) (fun i =>
        E (v (i + 1)) *
          ((w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
            (w (Y (i + 1)) -
              w (riskProcess X x D (v (i + 1)) ω)))) +
      E ρ * (w (riskProcess X x D ρ ω) -
        w (x + X.X ρ ω - rightLimit D ρ ω)) +
      F) (0 : ℝ) ≤ B := by sorry
