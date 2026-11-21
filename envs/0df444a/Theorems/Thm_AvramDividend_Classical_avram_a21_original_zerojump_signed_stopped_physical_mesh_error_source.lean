-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_zerojump_signed_stopped_physical_mesh_error_source
-- name    : AvramDividend.Classical.avram_a21_original_zerojump_signed_stopped_physical_mesh_error_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T07:45:52.590181+00:00
-- url     : https://prove2.me/theorems/3e964d5f-03df-4e8e-8289-b767b3161e52
-- title:
--   Original zerojump finitecap true stopped physical Gaussian signed mesh error source
-- statement:
--   Construct directly from the original Gaussian Levy process X and original admissible dividend D a finite physical stopped mesh with actual predictable Gaussian linear and Hessian coefficients, stopped increment M, and integrable Ito Taylor, cap-contact, ruin-contact and dividend residual error E_j of vanishing signed expectation. The pointwise original inclusive stopped cash F_k is bounded by w(x) plus actual Gaussian finite grid gains and E_j. The already proved 13c649df yields finite-grid conditional centring and integrability from these genuine physical hypotheses; the signed expected budget 282e follows by finite sum centring, leaving stochastic physical Ito construction as the substantive source.
-- source:
--   True original finitecap stopped Gaussian physical rightmesh Ito ledger. No source martingale, budget or target theorem assumed; expected martingale cancellation supplied by independent proved Gaussian source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_zerojump_signed_stopped_physical_mesh_error_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hν : X.ν = 0) (hFinite : C ≠ ⊤) :
    ∀ k, ∃
      (S : ℕ → Finset ℕ) (τg : ℕ → ℕ → Ω → ℝ≥0)
      (B h : ℕ → ℕ → ℝ≥0)
      (G H M : ℕ → ℕ → Ω → ℝ)
      (E : ℕ → Ω → ℝ)
      (hτg : ∀ j, ∀ i ∈ S j, ∀ s : ℝ≥0,
        MeasurableSet[𝓕.rightCont s] {ω : Ω | τg j i ω ≤ s}),
      (∀ j, ∀ i ∈ S j, ∀ ω, τg j i ω ≤ B j i) ∧
      (∀ j i (hi : i ∈ S j),
        Measurable[(isStoppingTime_withTop_of_le_events (τg j i)
          (hτg j i hi)).measurableSpace] (G j i)) ∧
      (∀ j i (hi : i ∈ S j),
        Measurable[(isStoppingTime_withTop_of_le_events (τg j i)
          (hτg j i hi)).measurableSpace] (H j i)) ∧
      (∀ j, M j = fun i ω =>
        (X.X (τg j i ω + h j i) ω -
          ((τg j i ω + h j i) : ℝ) * X.c) -
        (X.X (τg j i ω) ω - (τg j i ω : ℝ) * X.c)) ∧
      (∀ j, ∀ i ∈ S j, Integrable (fun ω => G j i ω * M j i ω) P) ∧
      (∀ j, ∀ i ∈ S j, Integrable (H j i) P) ∧
      (∀ j, ∀ i ∈ S j,
        Integrable (fun ω => H j i ω * (M j i ω)^2) P) ∧
      (∀ j, Integrable (E j) P) ∧
      Tendsto (fun j => ∫ ω, E j ω ∂P) atTop (nhds (0 : ℝ)) ∧
      (∀ j, ∀ᵐ ω ∂P,
        F k ω ≤ w x + (∑ i ∈ S j,
          (G j i ω * M j i ω +
            (H j i ω * (M j i ω)^2 -
              (h j i : ℝ) * X.σ^2 * H j i ω))) + E j ω) := by sorry
