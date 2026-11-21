-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_mixed_finitecap_fullmark_gaussian_physical_positive_excess
-- name    : AvramDividend.Classical.avram_freshD_original_mixed_finitecap_fullmark_gaussian_physical_positive_excess
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:41:06.23172+00:00
-- url     : https://prove2.me/theorems/242ca5f1-3937-4f98-b642-1f0f6c35a973
-- title:
--   Genuine finite-cap original mixed Lévy Gaussian grid and complete nonlinear marked compensation source with vanishing positive cash excess
-- statement:
--   The substantive missing finite-activity mixed Gaussian-jump physical source for the original dividend verification. At each genuinely ruin-clipped bounded stop and initial-filtration event, arbitrary positive cash-excess accuracy is witnessed by a finite bounded predictable Gaussian grid of the intrinsic original Gaussian residual together with the exact original whole-negative-mark compensated nonlinear value increment. The jump measure is built from original X and includes the full ruin overshoot, no small-band-only replacement. The original inclusive Stieltjes cash reward F is unchanged. Both genuine noise gains integrate to zero on the initial event; their combined positive error has arbitrarily small L1 mass. This is substantially stronger than the target expectation and exactly isolates the stochastic Ito localisation and ruin/cap boundary source that is still to be proved.
-- source:
--   Avram Dividend Classical original full-mark signed Ito cash verification, original stopped X, physical jump count NX, negative intensity ν, predictable intrinsic Gaussian mesh. Corrects deprecated 061f936f/5424c324 fixed-linear Jfull inequality by retaining the nonlinear w(Y+z)-w(Y) for ALL negative marks, generator/drift and dividend Stieltjes correction in the positive-excess estimate. Genuine source obligation for b98df424, not a conditional expected-cash-budget assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_mixed_finitecap_fullmark_gaussian_physical_positive_excess
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
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
    (n : ℕ) (hn : 0 < n)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (n : ℝ))).map Real.toNNReal
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if 0 < p.1.1 ∧ p.1.1 ≤ σ p.1.2 ∧
          (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
          0 ≤ Y p.1 ∧ ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1))
      else 0
    let J : Ω → ℝ := fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      ∀ ε : ℝ, 0 < ε →
      ∃ (R : ℝ≥0 → Ω → ℝ)
        (S : Finset ℕ) (a b : ℕ → ℝ≥0)
        (WG : ℕ → Ω → ℝ) (L : ℝ) (G : Ω → ℝ),
        (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
          Tendsto (fun j : ℕ =>
            avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
            atTop (𝓝 (R t ω))) ∧
        (∀ i ∈ S, a i ≤ b i ∧ b i ≤ (n : ℝ≥0)) ∧
        (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i)) ∧
        0 ≤ L ∧ (∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ L) ∧
        (∀ ω, G ω = ∑ i ∈ S,
          (if σ ω ≤ a i then 0 else WG i ω) *
            (R (b i) ω - R (a i) ω)) ∧
        IntegrableOn G A P ∧ IntegrableOn J A P ∧
        (∫ ω in A, G ω ∂P) = 0 ∧
        (∫ ω in A, J ω ∂P) = 0 ∧
        IntegrableOn (fun ω => max (F ω - w x - G ω - J ω) 0) A P ∧
        (∫ ω in A, max (F ω - w x - G ω - J ω) 0 ∂P) ≤ ε := by sorry
