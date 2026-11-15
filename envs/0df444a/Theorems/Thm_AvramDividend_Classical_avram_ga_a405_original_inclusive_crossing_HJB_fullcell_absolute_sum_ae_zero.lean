-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a405_original_inclusive_crossing_HJB_fullcell_absolute_sum_ae_zero
-- name    : AvramDividend.Classical.avram_ga_a405_original_inclusive_crossing_HJB_fullcell_absolute_sum_ae_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:07:11.26939+00:00
-- url     : https://prove2.me/theorems/9b3e590c-c73a-4956-98d6-2677946897fd
-- title:
--   Original inclusive Gaussian crossing full-cell HJB masked absolute sum converges to zero a.s.
-- statement:
--   For the original stopped Gaussian physical mesh, the unique genuine inclusive crossing cell's absolute compensated HJB/generator contribution converges almost surely to zero, with zero contribution when no cell crosses.
-- source:
--   Original a390 HJB source, Proved a396 uniform C2-generator coefficient budget, a398 scalar HJB envelope, a402 Gaussian centered full-cell crossing modulus.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a405_original_inclusive_crossing_HJB_fullcell_absolute_sum_ae_zero
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
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let CrossMask : ℕ → ℕ → Ω → Prop := fun m i ω =>
      s m i < ρ ω ∧ ρ ω ≤ s m i + Δ m
    let Err : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if CrossMask m i ω then
          let z := X.X (s m i + Δ m) ω - X.X (s m i) ω -
            (Δ m : ℝ) * X.c
          |Real.exp (-(q * (s m i : ℝ))) *
            (deriv w (x + X.X (s m i) ω - rightLimit D (s m i) ω) * z +
              (iteratedDeriv 2 w
                (x + X.X (s m i) ω - rightLimit D (s m i) ω) / 2) *
                (z^2 - (Δ m : ℝ) * X.σ^2)) +
            (Δ m : ℝ) * Real.exp (-(q * (s m i : ℝ))) *
              X.generator w (x + X.X (s m i) ω - rightLimit D (s m i) ω)|
        else 0
    ∀ᵐ ω ∂P, Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)) := by sorry
