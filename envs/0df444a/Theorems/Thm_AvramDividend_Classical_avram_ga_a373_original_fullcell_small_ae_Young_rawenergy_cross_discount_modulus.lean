-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a373_original_fullcell_small_ae_Young_rawenergy_cross_discount_modulus
-- name    : AvramDividend.Classical.avram_ga_a373_original_fullcell_small_ae_Young_rawenergy_cross_discount_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:35:51.034207+00:00
-- url     : https://prove2.me/theorems/d28d397f-3770-4c9b-9ca8-9638410f8086
-- title:
--   Original Gaussian true stopped small-cell combined positive source AE Young bound by uniform raw energy, Hessian cross and vanishing discount correction
-- statement:
--   For the actual original stopped Gaussian finite-horizon physical grid, there exist nonnegative L,M independent of mesh such that for any positive ε one can select a positive raw small-increment threshold δ with an almost-everywhere finite-mesh bound: positive combined small-source residual ≤ ε times original fully stopped raw squared-increment energy + M/2 times original fully stopped absolute raw-centred square cross energy + m(qΔ_m L)²/(2ε). This uses only the original one-sided Taylor, postpayment compact local Lipschitz and unweighted Hessian packages from a371, with AE finite-mask extension a372. The bound is the genuine analytic missing input to the expected-budget transfer a364, leading to a361 and closure of a216.
-- source:
--   Original actual X.X fullcell stopped a194+a369+a370 source via a371 and a368+a366 via a372, energy a367 and cross a214.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a371_original_fullcell_joint_Taylor_Lipschitz_Hessian_selected_cutoff_ae
import Theorems.Thm_AvramDividend_Classical_avram_ga_a372_ae_smallcell_to_fullmask_energy_cross_Young_source
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a373_original_fullcell_small_ae_Young_rawenergy_cross_discount_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let Small : ℝ → ℕ → Ω → ℝ := fun δ m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i =>
      E (s i) * (deriv w (Y (s i)) * R i +
        (iteratedDeriv 2 w (Y (s i)) / 2) * Z i^2)
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (w (Y (s i) + R i) - w (Y (s i))) - H i
    ∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω ∧ |R i| < δ then F i else 0
    let Energy : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        if s < ρ ω ∧ s + Δ ≤ ρ ω then R^2 else 0
    let Cross : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        let Z : ℝ := R - (Δ : ℝ) * X.c
        if s < ρ ω ∧ s + Δ ≤ ρ ω then |R^2 - Z^2| else 0
    ∃ L M : ℝ, 0 ≤ L ∧ 0 ≤ M ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ m : ℕ, ∀ᵐ ω ∂P,
          max (Small δ m ω) 0 ≤
            ε * Energy m ω + (M / 2) * Cross m ω +
              (m : ℝ) *
                (q * (((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) * L)^2 /
                  (2 * ε) := by sorry
