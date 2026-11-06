-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_inmeasure_physical_source_certificate
-- name    : AvramDividend.Classical.avram_limit2_original_inmeasure_physical_source_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:29:08.128194+00:00
-- url     : https://prove2.me/theorems/e08cf55b-04c9-41e7-8d6e-ec57d57af3b8
-- title:
--   Original compensated physical BV stopped-grid and in-measure cash convergence yield signed Fatou certificate
-- statement:
--   Given the exact original bounded-variation Lévy jump/drift compensated stopped-grid source, positive predictable localisation band, source identity, physical measurable nonnegative integrable cash grids and a bona fide convergence-in-measure to original strict pre-ruin cash plus terminal payoff, finite-grid expectation upper bounds produce the canonical six-clause signed Fatou witness. This is a weaker physical convergence requirement than L1, while keeping the full stochastic source interface.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_p3_e2_original_stopped_source_finite_grid_expected_upper
import Theorems.Thm_AvramDividend_Classical_avram_limit2_inmeasure_signed_certificate
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_limit2_original_inmeasure_physical_source_certificate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (Snn : ℝ≥0) (hSnn : (Snn : ℝ) = T)
    (τ : ℕ → Ω → ℝ≥0)
    (hτBound : ∀ n ω, τ n ω ≤ Snn)
    (hτ : ∀ n, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ n ω : WithTop ℝ≥0)))
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2)
    (hab : ∀ n, a n ≤ b n)
    (hBandWide : ∀ n, Icc ((a n) / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (E : ℕ → Set (ℝ≥0 × Ω))
    (hEm : ∀ n, MeasurableSet[𝓕.rightCont.predictable] (E n))
    (hEregion : ∀ n, ∀ p ∈ E n,
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n))
    (Mmesh Bmesh Fmesh : ℕ → Ω → ℝ)
    (hSource : ∀ n, let Upre : ℝ≥0 × Ω → ℝ := (fun p : ℝ≥0 × Ω =>
    Function.leftLim (fun v : ℝ≥0 =>
      x + X.X v p.2 - rightLimit D v p.2) p.1);
  let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := (fun p : (ℝ≥0 × Ω) × ℝ =>
    if p.1 ∈ E n ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
       (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
        w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
    else 0);
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
    fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ n p.1.2 : ℝ≥0∞) then G p else 0;
  let F : ℝ≥0 × Ω → ℝ := (fun p : ℝ≥0 × Ω =>
    if p ∈ E n then Real.exp (-(q * (p.1 : ℝ))) *
      (X.drift * deriv w (Function.leftLim (fun v : ℝ≥0 =>
          x + X.X v p.2 - rightLimit D v p.2) p.1) +
       (∫ z in Iio (0 : ℝ),
          w (Function.leftLim (fun v : ℝ≥0 =>
            x + X.X v p.2 - rightLimit D v p.2) p.1 + z) -
          w (Function.leftLim (fun v : ℝ≥0 =>
            x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) -
       q * w (Function.leftLim (fun v : ℝ≥0 =>
          x + X.X v p.2 - rightLimit D v p.2) p.1))
    else 0);
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict
{u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω -
Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)));
  let M : Ω → ℝ := fun ω => (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ t, ∫ z, H ((t, ω), z)
∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 (Snn : ℝ))).map Real.toNNReal));
  let B : Ω → ℝ := fun ω => (∫ t, F (t, ω) ∂(((volume : Measure ℝ).restrict (Icc 0 (Snn : ℝ))).map Real.toNNReal));
  Mmesh n = M ∧ Bmesh n = B)
    (hFm : ∀ n, Measurable (Fmesh n))
    (hFi : ∀ n, Integrable (Fmesh n) P)
    (hFn : ∀ n, 0 ≤ᵐ[P] Fmesh n)
    (hBudget : ∀ n, ∀ᵐ ω ∂P,
      Fmesh n ω ≤ w x + (Mmesh n ω + Bmesh n ω))
    (R : Ω → ℝ)
    (hMeasure : TendstoInMeasure P Fmesh atTop R) :
    ∃ F M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ w x + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        ENNReal.ofReal (R ω) ≤
          liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by sorry
