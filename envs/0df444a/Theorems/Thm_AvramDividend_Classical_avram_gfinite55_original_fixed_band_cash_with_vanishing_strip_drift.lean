-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite55_original_fixed_band_cash_with_vanishing_strip_drift
-- name    : AvramDividend.Classical.avram_gfinite55_original_fixed_band_cash_with_vanishing_strip_drift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T22:47:41.782202+00:00
-- url     : https://prove2.me/theorems/d54d941c-1ea7-41bb-b2b4-10a7d4289cf2
-- title:
--   Original finite-cap fixed-band Gaussian cash ledger with vanishing cap-strip drift
-- statement:
--   Corrected fixed-band original-process Itô-Stieltjes Gaussian ledger. For each deterministic cap cutoff b_j and arbitrary accuracy, find an arbitrarily fine physical grid whose positive expected cash error is bounded by the endpoint cap-linear corner defect, a single j-dependent vanishing strip allowance eta_j arising from occupation of b_j<Y<C, and epsilon. This isolates the actual finite-grid stochastic cash step from diagonal selection; the previous theta_j+epsilon-only fixed-band statement omitted the possible upper-strip generator drift.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gfinite55_original_fixed_band_cash_with_vanishing_strip_drift
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
      ∃ (η : ℕ → ℝ),
        Tendsto η atTop (𝓝 (0 : ℝ)) ∧
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
        ∃ E : Ω → ℝ,
          IntegrableOn E A P ∧
          (∀ᵐ ω ∂(P.restrict A), F ω ≤ w x + M ω + E ω) ∧
          (∫ ω in A, max (E ω) 0 ∂P) ≤
            (w C.toReal - w b) - (C.toReal - b) + η j + ε := by
  sorry
