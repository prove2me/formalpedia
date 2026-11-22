-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_original_canonical_stopped_gaussian_mesh_physical_positive_L1_source
-- name    : AvramDividend.Classical.avram_a24_original_canonical_stopped_gaussian_mesh_physical_positive_L1_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T17:03:45.198296+00:00
-- url     : https://prove2.me/theorems/4f334c57-baf4-4044-8a70-92b31530f229
-- title:
--   Original positive-clock finite-cap Gaussian Ito-Stieltjes physical clipped uniform grid source
-- statement:
--   Construct on the original zero-jump unbounded-variation Lévy surplus and actual stopped dividend reward the canonical finite physical Brownian grid: bounded start times are the minimum of the actual selected stopped time and the original deterministic uniform times, with deterministic step equal to the horizon divided by mesh count, fixed initial-horizon bounds, and all stochastic integrands predictable with their exact original centred Gaussian increments. Prove the physical signed Ito-Stieltjes positive-excess L1 limit for the actual discounted post-right-dividend terminal and inclusive right-payment cash. The finite-grid positive-part integrability then follows separately from the already proved general finite mesh lemma; this child contains the genuinely missing stochastic source limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a24_original_canonical_stopped_gaussian_mesh_physical_positive_L1_source
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
      (∀ j, S j = Finset.range (j + 1)) ∧
      (∀ j i ω, τg j i ω =
        min ((i : ℝ≥0) * ((n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)))
          (σ k ω)) ∧
      (∀ j i, B j i = (n : ℝ≥0)) ∧
      (∀ j i, h j i =
        (n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ∧
      Tendsto (fun j => ∫ ω,
        max (F k ω - w x - (∑ i ∈ S j,
          (G j i ω * M j i ω +
            (H j i ω * (M j i ω)^2 -
              (h j i : ℝ) * X.σ^2 * H j i ω)))) 0 ∂P)
        atTop (nhds (0 : ℝ)) := by sorry
