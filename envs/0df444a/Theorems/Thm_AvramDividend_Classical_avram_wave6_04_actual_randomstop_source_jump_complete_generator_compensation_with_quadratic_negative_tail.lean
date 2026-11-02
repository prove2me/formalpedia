-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_randomstop_source_jump_complete_generator_compensation_with_quadratic_negative_tail
-- name    : AvramDividend.Classical.avram_wave6_04_actual_randomstop_source_jump_complete_generator_compensation_with_quadratic_negative_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T00:02:22.302324+00:00
-- url     : https://prove2.me/theorems/e5314fb8-33fe-4327-bfd1-e275df6c2d67
-- title:
--   Complete literal source stopped compensated nonlinear jump expectation, generator, and all signed quadratic negative-mark tails
-- statement:
--   Strengthens the original-source randomly stopped discounted nonlinear C2 negative-jump generator interface with the source Lévy full-negative-mark *quadratic* generator tail limit. Its eleven conjuncts simultaneously yield literal X.X jump-sum integrability and generator expectation, signed predictable full negative source Taylor and generator product L1/L2 energies, both Taylor L1/L2 and source generator L1/L2 decreasing-mark tails, and physical time-clock L1 drift-tail convergence. Still assumes exact future rectangle source transport and genuine time-clock transport; no generic predictable-clock source-intensity shortcut.
-- source:
--   Chat04 strengthened Chat06 all-in-one source compensation interface by Proved 0d791eda original expectation package and Proved 2a64513d signed quadratic generator negative-mark tails.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_randomstop_source_jump_complete_generator_compensation_interface
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_original_rightcont_randomly_stopped_discount_weight_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_signed_predictable_generator_kernel_full_negative_mark_L2_tail

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_randomstop_source_jump_complete_generator_compensation_with_quadratic_negative_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
  :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ)) := fun ω =>
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω)
    ∀     (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (T : ℝ≥0)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hST : S = {p | p.1.1 ≤ T})
    (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (B : ℕ → Set ℝ) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hLocal : ∀ k, MT ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B k) ≠ ∞)
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕.rightCont i] A → MeasurableSet C →
      MT ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C))
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕.rightCont τ)
    (q : ℝ) (hq : 0 ≤ q)
    (A : ℕ → Set ℝ)
    (hAm : ∀ n, MeasurableSet (A n))
    (hAneg : ∀ n, A n ⊆ Iio (0 : ℝ))
    (hAanti : Antitone A)
    (hAempty : (⋂ n, A n) = ∅),
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0) *
      (if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0)
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let J : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * J p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    let GG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * JG p
    Integrable (fun ω =>
      ∫ p, GW ((p.1, ω), p.2) ∂(NX ω)) P ∧
    (∫ ω, (∫ p, GW ((p.1, ω), p.2) ∂(NX ω)) ∂P) =
      (∫ p : ℝ≥0 × Ω,
        a p * (∫ z in Iio (0 : ℝ), JG (p, z) ∂X.ν) ∂μ) ∧
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal (|GW p|)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤) ∧
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal ((GW p) ^ 2)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤) ∧
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal (|GG p|)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤) ∧
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal ((GG p) ^ 2)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤) ∧
    (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in A n, ENNReal.ofReal (|a p * HS (p,z)|) ∂X.ν ∂μ) = 0 ∧
    (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in A n, ENNReal.ofReal ((a p * HS (p,z)) ^ 2) ∂X.ν ∂μ) = 0 ∧
    (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in A n, ENNReal.ofReal (|a p * JG (p,z)|) ∂X.ν ∂μ) = 0 ∧
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ‖a p * (∫ z in A n, JG (p,z) ∂X.ν)‖ₑ ∂
      (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
      atTop (𝓝 0) ∧
    (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in A n, ENNReal.ofReal ((a p * JG (p,z)) ^ 2) ∂X.ν ∂μ) = 0 := by sorry
