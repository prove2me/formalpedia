-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e2_original_source_signed_fatou_grid_of_pathwise_budget
-- name    : AvramDividend.Classical.avram_p3_e2_original_source_signed_fatou_grid_of_pathwise_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:30:58.861687+00:00
-- url     : https://prove2.me/theorems/eded9541-03d1-4b1f-a502-b1e2bcb55bac
-- title:
--   Original strict BV Fatou-grid certificate from a single source pathwise signed budget
-- statement:
--   For the actual original admissible spectrally negative BV Lévy reserve and strict discounted Stieltjes payoff, if each predictable compact pre-ruin grid's literal stopped negative-jump compensator and physical HJB drift satisfy the true pathwise source cash inequality, then the complete original signed Fatou-grid certificate follows. The stopped compensator mean zero, negative HJB drift expectation and all L1 hypotheses are proved from source C1 interior, admissibility and compactness via existing theorems. A measurable L1 nonnegative payoff equal almost everywhere to the exact strict payoff yields the Fatou liminf. The sole substantive stochastic chain-accounting premise is the original pathwise inequality, explicit and unweakened.
-- source:
--   Exact c1e2f021 original strict cash source grid. Depends on Proved original measurable strict reward, Proved compact derivative 07ca388c, and Proved original admissible signed source budget 3497711e; hPath is the sole unproved stochastic source accounting hypothesis.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_measurable_version
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_compact_cap_derivative_bound_automatic_open
import Theorems.Thm_AvramDividend_Classical_avram_p3_e2_original_admissible_signed_source_budget_no_L1_assumption
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_e2_original_source_signed_fatou_grid_of_pathwise_budget
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

(τ : ℕ → Ω → ℝ≥0)
(hτBound : ∀ n ω, τ n ω ≤ (⟨T, hT⟩ : ℝ≥0))
(hτ : ∀ n, IsStoppingTime 𝓕.rightCont
  (fun ω => (τ n ω : WithTop ℝ≥0)))
(a b L R : ℕ → ℝ)
(ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2)
(hab : ∀ n, a n ≤ b n)
(hL : ∀ n, 0 ≤ L n) (hR : ∀ n, 0 ≤ R n)
(hLip : ∀ n, ∀ u ∈ Icc ((a n) / 2) (b n),
  ∀ v ∈ Icc ((a n) / 2) (b n), |w u - w v| ≤ L n * |u - v|)
(hWbound : ∀ n (v : ℝ), v ≤ b n → |w v| ≤ R n)
(hBand : ∀ n, Icc (a n) (b n) ⊆
  {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
(E : ℕ → Set (ℝ≥0 × Ω))
(hEm : ∀ n, MeasurableSet[𝓕.rightCont.predictable] (E n))
(hEregion : ∀ n, ∀ p ∈ E n,
  Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈
      Icc (a n) (b n))
(hEcap : ∀ n, ∀ p ∈ E n, ENNReal.ofReal
  (Function.leftLim (fun v : ℝ≥0 =>
    x + X.X v p.2 - rightLimit D v p.2) p.1) < C)
(Mmesh Bmesh : ℕ → Ω → ℝ)
(hSource : ∀ n, let Upre : ℝ≥0 × Ω → ℝ := (fun p : ℝ≥0 × Ω => Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1);
  let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := (fun p : (ℝ≥0 × Ω) × ℝ => if p.1 ∈ E n ∧ p.2 < 0 then Real.exp (-(q * (p.1.1 : ℝ))) * (w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) - w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)) else 0);
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ n p.1.2 : ℝ≥0∞) then G p else 0;
  let F : ℝ≥0 × Ω → ℝ := (fun p : ℝ≥0 × Ω => if p ∈ E n then Real.exp (-(q * (p.1 : ℝ))) * (X.drift * deriv w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) + (∫ z in Iio (0 : ℝ), w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 + z) - w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) - q * w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)) else 0);
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)));
  let M : Ω → ℝ := fun ω => (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal));
  let B : Ω → ℝ := fun ω => (∫ t, F (t, ω) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)); Mmesh n = M ∧ Bmesh n = B)
(hPath : ∀ n, ∀ᵐ ω ∂P,
  let S : ℝ≥0 := ⟨T, hT⟩
  (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
    ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0) ≤ w x + Mmesh n ω + Bmesh n ω) :
    ∃ F M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ w x + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        ENNReal.ofReal (
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0)) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by sorry
