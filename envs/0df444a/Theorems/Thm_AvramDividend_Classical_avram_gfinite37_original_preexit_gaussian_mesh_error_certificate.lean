-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite37_original_preexit_gaussian_mesh_error_certificate
-- name    : AvramDividend.Classical.avram_gfinite37_original_preexit_gaussian_mesh_error_certificate
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T13:19:10.414427+00:00
-- url     : https://prove2.me/theorems/2cedcbff-276b-4472-8789-5417f2ea1949
-- title:
--   Original finite-cap Gaussian stopped physical-grid positive error vanishes on initial events
-- statement:
--   Construct the deterministic original-X finite Gaussian grid on the same probability space, using the original post-rightpayment reserve, cap-affine first and second derivative coefficients, and the actual stopping time. Prove initial-event centring of the exact source Gaussian residual and a nonnegative integrable residual upper bound for the actual strict-pre-ruin dividend cash plus postpayment stopped terminal value, whose event integral vanishes as the mesh is refined. This is the remaining physical Itô/Stieltjes certificate required by 40ec25bd.
-- source:
--   Root-connected necessary child for 40ec25bd. Source-exact Gaussian increments of the original X and original D on original Omega/P, with cap-affine gradient, positive reward residual and initial-event L1 convergence. No auxiliary process or arbitrary-grid claim.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gfinite37_original_preexit_gaussian_mesh_error_certificate
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
      ∃ (G H : ℕ → ℕ → Ω → ℝ) (E : ℕ → Ω → ℝ),
        let Δ : ℕ → ℝ≥0 := fun j => (n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℕ → ℝ≥0 := fun j i => (i : ℝ≥0) * Δ j
        let Y : ℕ → ℕ → Ω → ℝ := fun j i ω =>
          x + X.X (s j i) ω - rightLimit D (s j i) ω
        let Z : ℕ → ℕ → Ω → ℝ := fun j i ω =>
          X.X (s j i + Δ j) ω - X.X (s j i) ω - (Δ j : ℝ) * X.c
        let M : ℕ → Ω → ℝ := fun j ω =>
          (Finset.range (j + 1)).sum (fun i =>
            G j i ω * Z j i ω + H j i ω *
              (Z j i ω ^ 2 - (Δ j : ℝ) * X.σ ^ 2))
        let F : Ω → ℝ := fun ω =>
          if ρ ω = 0 then w x else
            Real.exp (-(q * (ρ ω : ℝ))) *
              w (riskProcess X x D (ρ ω) ω) +
            (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
              ENNReal.ofReal (Real.exp (-(q * z)))
              ∂(dividendMeasure D ω)).toReal
        (∀ j i ω, G j i ω = if s j i < ρ ω then
          Real.exp (-(q * (s j i : ℝ))) *
            (if 0 < Y j i ω ∧ ENNReal.ofReal (Y j i ω) < C
             then deriv w (Y j i ω) else 1) else 0) ∧
        (∀ j i ω, H j i ω = if s j i < ρ ω then
          (1 / 2 : ℝ) * Real.exp (-(q * (s j i : ℝ))) *
            (if 0 < Y j i ω ∧ ENNReal.ofReal (Y j i ω) < C
             then iteratedDeriv 2 w (Y j i ω) else 0) else 0) ∧
        (∀ j, IntegrableOn (M j) A P) ∧
        (∀ j, IntegrableOn (E j) A P) ∧
        (∀ j, (∫ ω in A, M j ω ∂P) = 0) ∧
        (∀ j, ∀ᵐ ω ∂(P.restrict A), 0 ≤ E j ω) ∧
        (∀ j, ∀ᵐ ω ∂(P.restrict A),
          F ω ≤ w x + M j ω + E j ω) ∧
        Tendsto (fun j => ∫ ω in A, E j ω ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
