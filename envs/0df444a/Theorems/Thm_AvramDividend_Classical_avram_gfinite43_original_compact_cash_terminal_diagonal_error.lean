-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite43_original_compact_cash_terminal_diagonal_error
-- name    : AvramDividend.Classical.avram_gfinite43_original_compact_cash_terminal_diagonal_error
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T13:47:39.0056+00:00
-- url     : https://prove2.me/theorems/46781d63-8705-4655-a55a-ff678dcb2f1f
-- title:
--   Original finite-cap compact diagonal Itô-Stieltjes cash error tends to zero
-- statement:
--   Construct an increasing diagonal mesh and the nonnegative L1 error bounding actual original strict cash plus postpayment terminal reward by the initial value and compact-masked Gaussian grid. Prove the true Itô-Stieltjes ledger, cap-corner local-time sign, ruin and horizon boundaries, and convergence as the cap cutoff approaches C without asserting uncut Hessian moments.
-- source:
--   Two sound compact-localisation children for gfinite41, root-connected to 40ec25bd and finite Gaussian 6eb9cc6a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gfinite43_original_compact_cash_terminal_diagonal_error
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
      ∃ (N : ℕ → ℕ) (E : ℕ → Ω → ℝ),
        let Δ : ℕ → ℝ≥0 := fun j =>
          (n : ℝ≥0) / ((N j + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℕ → ℝ≥0 := fun j i => (i : ℝ≥0) * Δ j
        let a : ℝ := δ / 2
        let b : ℕ → ℝ := fun j =>
          C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → ℕ → Ω → ℝ := fun j i ω =>
          x + X.X (s j i) ω - rightLimit D (s j i) ω
        let Z : ℕ → ℕ → Ω → ℝ := fun j i ω =>
          X.X (s j i + Δ j) ω - X.X (s j i) ω - (Δ j : ℝ) * X.c
        let G : ℕ → ℕ → Ω → ℝ := fun j i ω =>
          if s j i < ρ ω then Real.exp (-(q * (s j i : ℝ))) *
            (if Y j i ω ∈ Icc a (b j) then deriv w (Y j i ω)
             else 1) else 0
        let H : ℕ → ℕ → Ω → ℝ := fun j i ω =>
          if s j i < ρ ω then (1 / 2 : ℝ) *
            Real.exp (-(q * (s j i : ℝ))) *
            (if Y j i ω ∈ Icc a (b j)
             then iteratedDeriv 2 w (Y j i ω) else 0) else 0
        let M : ℕ → Ω → ℝ := fun j ω =>
          (Finset.range (N j + 1)).sum (fun i =>
            G j i ω * Z j i ω + H j i ω *
              (Z j i ω ^ 2 - (Δ j : ℝ) * X.σ ^ 2))
        let F : Ω → ℝ := fun ω =>
          if ρ ω = 0 then w x else
            Real.exp (-(q * (ρ ω : ℝ))) *
              w (riskProcess X x D (ρ ω) ω) +
            (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
              ENNReal.ofReal (Real.exp (-(q * z)))
              ∂(dividendMeasure D ω)).toReal
        StrictMono N ∧
        (∀ j, IntegrableOn (E j) A P) ∧
        (∀ j, ∀ᵐ ω ∂(P.restrict A), 0 ≤ E j ω) ∧
        (∀ j, ∀ᵐ ω ∂(P.restrict A),
          F ω ≤ w x + M j ω + E j ω) ∧
        Tendsto (fun j => ∫ ω in A, E j ω ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
