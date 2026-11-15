-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24x2_ruinclipped_true_physical_precontact_signed_cash_HJB_sum
-- name    : AvramDividend.Classical.avram_b24x2_ruinclipped_true_physical_precontact_signed_cash_HJB_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:41:39.934254+00:00
-- url     : https://prove2.me/theorems/d7c57b16-df7d-4178-87a2-53ff6041085f
-- title:
--   Original clipped strict-pre-ruin physical mesh HJB and Stieltjes cash joint signed bound, with admissibility and gradient hypotheses
-- statement:
--   On each pre-ruin physical mesh cell, combine the actual original generator HJB nonpositive term and the admissible right-payment sign with the full discounted Stieltjes payout and cap-linear reserve loss. The resulting joint signed sum is bounded by the exact left-to-right discount-weight correction. The theorem preserves the original X, D, strict ruin clipping and finite-grid payment measure.
-- source:
--   Repairs B24x with exactly the necessary admissibility, C1 and derivative-gradient premises required by the published physical discounted Stieltjes lemma B241, then sums B239 signed generator and right-payment nonpositivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24x2_ruinclipped_true_physical_precontact_signed_cash_HJB_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ η (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D η) →
      rightLimit D t η - D t η ≤
        w (riskProcess X x D t η) -
          w (riskProcess X x D t η -
            (rightLimit D t η - D t η)))
    (σ : Ω → ℝ≥0) (n m : ℕ) (ω : Ω)
    (active : ℕ → Bool)
    (hInterior : ∀ i ∈ Finset.range m, active i = true →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (σ ω)
      let z := riskProcess X x D (v i) ω
      0 < z ∧ ENNReal.ofReal z < C)
    (hTimes : ∀ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (σ ω)
      v i ≤ v (i + 1))
    (R : Finset ℝ≥0)
    (hPre : ∀ u ∈ R,
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω)
    (hCellPre : ∀ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (σ ω)
      v (i+1) = 0 ∨ (v (i+1) : ℝ≥0∞) < ruinTime X x D ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let H : ℝ := ∑ i ∈ Finset.range m, if active i then
      Real.exp (-(q * (v i : ℝ))) *
        ((v (i+1) : ℝ) - (v i : ℝ)) *
        (X.generator w (riskProcess X x D (v i) ω) -
          q * w (riskProcess X x D (v i) ω)) else 0
    let J : ℝ := ∑ u ∈ R, Real.exp (-(q * (u : ℝ))) *
      ((rightLimit D u ω - D u ω) -
        (w (riskProcess X x D u ω) -
         w (riskProcess X x D u ω - (rightLimit D u ω - D u ω))))
    let Cash : ℝ := ∑ i ∈ Finset.range m,
      (      (∫⁻ t in Ioc (v i : ℝ) (v (i+1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (v (i+1) : ℝ))) *
        (V (x + X.X (v (i+1)) ω - rightLimit D (v (i+1)) ω) -
         V (x + X.X (v (i+1)) ω - rightLimit D (v i) ω)))
    let Err : ℝ := ∑ i ∈ Finset.range m,
      (Real.exp (-(q * (v i : ℝ))) -
       Real.exp (-(q * (v (i+1) : ℝ)))) *
        (V (x + X.X (v (i+1)) ω - rightLimit D (v i) ω) -
         V (x + X.X (v (i+1)) ω - rightLimit D (v (i+1)) ω))
    H + J + Cash ≤ Err := by sorry
