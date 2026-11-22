-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerF_original_rightmesh_positive_clock_restricted_ennreal_expected_budget_v1
-- name    : AvramDividend.Classical.avram_pj_workerF_original_rightmesh_positive_clock_restricted_ennreal_expected_budget_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T21:17:16.495382+00:00
-- url     : https://prove2.me/theorems/bc89df64-f7ca-4b30-b405-37aef4d1391d
-- title:
--   Original positive right-mesh stopped caplinear terminal and inclusive dividend reward has event-restricted HJB budget
-- statement:
--   For the genuine original unbounded-variation spectrally negative Lévy process, HJB supersolution, admissible dividend strategy and right-mesh clock ρ=min(ruin-clipped τ, σk+1/(m+1)), the expected nonnegative real caplinear terminal plus full inclusive Stieltjes cash on the strictly positive-clock event {ρ≠0} is bounded by w(x) times its probability. This is the positive-time original stopped Ito-Meyer/Stieltjes source estimate, retaining all physical jump, Gaussian, generator and right-payment terms. The ρ=0 atom is handled separately from already Proved initial-payment inequalities.
-- source:
--   Faithful strictly-positive-clock event restriction of the original source budget theorem 5ce08aeb-a676-4f3c-94ea-016cc05ec7a6. No new regularity, model or assumptions. Target is to be connected immediately by a proof sketch of that parent.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerF_original_rightmesh_positive_clock_restricted_ennreal_expected_budget_v1
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
    (hFI : ∀ k, Integrable (F k) P) :
    ∀ (k m : ℕ),
      let ρ : Ω → ℝ≥0 := fun ω =>
        min (τ ω) (σ k ω + ((1 : ℝ≥0) / ((m : ℝ≥0) + 1)))
      let V : ℝ → ℝ := fun z =>
        if ENNReal.ofReal z ≤ C then w z
        else w C.toReal + (z - C.toReal)
      let Approx : Ω → ℝ := fun ω =>
        Real.exp (-(q * (ρ ω : ℝ))) *
          V (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
               x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
             else riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      (∫⁻ ω in {ω : Ω | ρ ω ≠ 0},
        ENNReal.ofReal (Approx ω) ∂P) ≤
      ENNReal.ofReal (w x) * P {ω : Ω | ρ ω ≠ 0} := by sorry
