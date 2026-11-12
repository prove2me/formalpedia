-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger161_original_clipped_discount_euler_pathwise_rate
-- name    : AvramDividend.Classical.avram_gledger161_original_clipped_discount_euler_pathwise_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T21:04:11.646008+00:00
-- url     : https://prove2.me/theorems/22928a5c-e99c-4176-8b60-7da19f1ce067
-- title:
--   Original stopped postpayment discount Euler error has a deterministic vanishing pathwise rate
-- statement:
--   Original clipped stopping time and postpayment reserve source yield a uniform almost-sure pathwise O(1/(m+1)) Euler error bound. The finite clipped grid splits into complete interior cells and one crossing cell, including rho=0, and compact C2 local bounds provide a deterministic weight bound.
-- source:
--   Strict source-exact Gaussian gledger139 decomposition; Proved original postpayment band gledger137 and Proved weighted finite clipped Euler bound gledger149. Parent gledger139 imports both gledger160 and gledger161.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger161_original_clipped_discount_euler_pathwise_rate
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
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ᵐ ω ∂P, |A m ω| ≤ K / ((m : ℝ) + 1) := by sorry
