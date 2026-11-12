-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger139_original_clipped_postpayment_discount_euler_absolute_L1
-- name    : AvramDividend.Classical.avram_gledger139_original_clipped_postpayment_discount_euler_absolute_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:11:16.783266+00:00
-- url     : https://prove2.me/theorems/c0442656-935b-4327-b9a8-75b6ecc3a89a
-- title:
--   Original compact stopped Gaussian mesh discount Euler error vanishes in absolute L1
-- statement:
--   For the original clipped stopped Gaussian mesh and genuine postpayment source Y=x+X.X-rightLimit D, the discounted time increment is asymptotic in absolute L1 to minus q times the uniformly spaced interior clock step. The theorem isolates the clock-discount Euler component of gledger50, including the final clipped crossing cell and its time-zero case; it does not concern the physical Taylor spatial/noise term.
-- source:
--   A proper strict sub-obligation of gledger50 original Taylor positive L1. Use the source-specific Proved gledger137 compact postpayment prefix band and Proved gledger68 clipped source envelope; bound exponential Euler error on the deterministic uniform clipped grid, isolate the single crossing cell and exploit finite original P.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger139_original_clipped_postpayment_discount_euler_absolute_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let A : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      (∑ i ∈ Finset.range (m + 1),
        (E (v (i + 1)) - E (v i)) * w (Y (v i))) +
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then q * (Δ : ℝ) * E s * w (Y s) else 0
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => |A m ω|) P ∧
      (∫ ω, |A m ω| ∂P) ≤ ε := by sorry
