-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite61_original_fixed_band_cash_with_explicit_occupation_cost
-- name    : AvramDividend.Classical.avram_gfinite61_original_fixed_band_cash_with_explicit_occupation_cost
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T23:12:28.674227+00:00
-- url     : https://prove2.me/theorems/1a7ef9d6-598e-4696-8cb5-8fa7bc5fabac
-- title:
--   Original finite Gaussian fixed-band cash estimate with explicit cap-strip occupation drift
-- statement:
--   Original same-space stopped finite-grid Ito-Stieltjes cash estimate, retaining upper-cap-strip cost as positive original drift times expected occupation of the strip and the terminal cap-linear corner defect. Choose cofinal fine mesh for each fixed band and epsilon. This is the remaining local stochastic ledger, separate from the occupation limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gfinite61_original_fixed_band_cash_with_explicit_occupation_cost
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ ω : WithTop ℝ≥0)))
      (hρle : ∀ ω, ρ ω ≤ σ k ω)
      (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      ∀ (j : ℕ) (ε : ℝ), 0 < ε →
      ∀ (K : ℕ), ∃ (m : ℕ), K < m ∧
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i ω =>
          x + X.X (s i) ω - rightLimit D (s i) ω
        let Z : ℕ → Ω → ℝ := fun i ω =>
          X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
        let G : ℕ → Ω → ℝ := fun i ω =>
          if s i < ρ ω then Real.exp (-(q * (s i : ℝ))) *
            (if Y i ω ∈ Icc a b then deriv w (Y i ω) else 1) else 0
        let H : ℕ → Ω → ℝ := fun i ω =>
          if s i < ρ ω then (1 / 2 : ℝ) *
            Real.exp (-(q * (s i : ℝ))) *
            (if Y i ω ∈ Icc a b
             then iteratedDeriv 2 w (Y i ω) else 0) else 0
        let M : Ω → ℝ := fun ω =>
          (Finset.range (m + 1)).sum (fun i =>
            G i ω * Z i ω + H i ω *
              (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
        let F : Ω → ℝ := fun ω =>
          if ρ ω = 0 then w x else
            Real.exp (-(q * (ρ ω : ℝ))) *
              w (riskProcess X x D (ρ ω) ω) +
            (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
              ENNReal.ofReal (Real.exp (-(q * z)))
              ∂(dividendMeasure D ω)).toReal
        let Occ : Ω → ℝ := fun ω =>
          ∫ t in Ioo (0 : ℝ) (n : ℝ),
            if t < (ρ ω : ℝ) ∧
                b < riskProcess X x D (Real.toNNReal t) ω
            then (1 : ℝ) else 0 ∂volume
        (∫ ω in A, max (F ω - w x - M ω) 0 ∂P) ≤
          (w C.toReal - w b) - (C.toReal - b) +
            max X.c 0 * (∫ ω in A, Occ ω ∂P) + ε := by
  sorry
