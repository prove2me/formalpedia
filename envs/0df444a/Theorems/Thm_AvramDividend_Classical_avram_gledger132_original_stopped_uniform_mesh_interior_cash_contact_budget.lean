-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger132_original_stopped_uniform_mesh_interior_cash_contact_budget
-- name    : AvramDividend.Classical.avram_gledger132_original_stopped_uniform_mesh_interior_cash_contact_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:48:27.223403+00:00
-- url     : https://prove2.me/theorems/bde38b1c-2a14-48e1-a400-a20aecef1a49
-- title:
--   Original positive stopped clock interior cash and contact sum obeys the clipped-mesh rate bound
-- statement:
--   For the original X and D and a strictly positive ruin-clipped stopping clock, the first crossing of the deterministic clipped mesh determines the genuine strict interior cells. Their original contact losses plus actual discounted cell Stieltjes cash obey the proved compact-prefix rate bound. The theorem returns the crossing index and post-crossing tail identities for subsequent boundary accounting.
-- source:
--   Instantiates Proved gledger112 on the original mesh, Proved gledger110 first crossing and gledger89 monotonicity; gledger131 provides the exact width of strict interior cells. No expectation or independent stochastic process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger132_original_stopped_uniform_mesh_interior_cash_contact_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (n m : ℕ) (ρ : ℝ≥0) (hρpos : 0 < ρ) (hρn : ρ ≤ (n : ℝ≥0))
    (hρruin : (ρ : ℝ≥0∞) ≤ ruinTime X x D ω)
    (u : ℝ) (hu : 0 ≤ u)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ → u ≤ riskProcess X x D t ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    ∃ k : ℕ, k < m + 2 ∧ v k < ρ ∧ v (k + 1) = ρ ∧
      (∀ i : ℕ, i < k → v (i + 1) < ρ) ∧
      (∀ i : ℕ, k < i → v i = ρ) ∧
      (∑ i ∈ Finset.range k,
        Real.exp (-(q * (v (i + 1) : ℝ))) *
          (w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
           w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω))) +
      (∑ i ∈ Finset.range k,
        (∫⁻ s in Ioc (v i : ℝ) (v (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) ≤
      q * (Δ : ℝ) * Real.exp (q * (n : ℝ)) *
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by sorry
