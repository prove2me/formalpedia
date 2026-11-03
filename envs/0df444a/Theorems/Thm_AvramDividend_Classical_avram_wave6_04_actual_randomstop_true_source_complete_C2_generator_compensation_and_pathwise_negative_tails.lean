-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_randomstop_true_source_complete_C2_generator_compensation_and_pathwise_negative_tails
-- name    : AvramDividend.Classical.avram_wave6_04_actual_randomstop_true_source_complete_C2_generator_compensation_and_pathwise_negative_tails
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:17:17.216466+00:00
-- url     : https://prove2.me/theorems/6ea81238-fc68-44ac-a798-b86b68cc9776
-- title:
--   Complete original stopped C2 source generator compensation and all pathwise negative Taylor tails
-- statement:
--   Full original-source compensated nonlinear C2 negative-jump generator package for Chat06: expected stopped discounted original Lévy jump Taylor sum is integrable and its drift equals the physical SpectrallyNegativeLevy.generatorIntegrand contribution; for almost every actual original X sample path the kernel is absolutely and quadratically summable, and its signed, absolute and quadratic decreasing negative-mark cutoff tails vanish. It uses source intrinsic NX, prepayment left reserve Y, actual inclusive ruinTime, C2 interior localisation and negative extension of w. hFuture and hμclock remain explicit source-time assumptions, to be supplied by Chat01; separate Chat02 martingale isometry, Chat03 Gaussian calculus and Chat05 dividend-control jumps are not asserted.
-- source:
--   Wave6 Chat04 complete Chat06 source compensated generator plus pathwise energy and marked tail assembly. Declaration-only preamble omits a proof-only Open dependency; the proof source retains its full import and is submitted only once that dependency is Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_randomstop_source_jump_complete_generator_compensation_with_quadratic_negative_tail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_randomstop_true_source_complete_C2_generator_compensation_and_pathwise_negative_tails
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
    (A : ℕ → Set ℝ) (hAm : ∀ n, MeasurableSet (A n))
    (hAneg : ∀ n, A n ⊆ Iio (0 : ℝ))
    (hAanti : Antitone A) (hAempty : (⋂ n, A n) = ∅),
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
    let AT : ℕ → Set (ℝ≥0 × ℝ) := fun n => {p | p.2 ∈ A n}
    let F : Ω → (ℝ≥0 × ℝ) → ℝ := fun ω p => GW ((p.1, ω), p.2)
    Integrable (fun ω =>
      ∫ p, GW ((p.1, ω), p.2) ∂(NX ω)) P ∧
    (∫ ω, (∫ p, GW ((p.1, ω), p.2) ∂(NX ω)) ∂P) =
      (∫ p : ℝ≥0 × Ω,
        a p * (∫ z in Iio (0 : ℝ), JG (p, z) ∂X.ν) ∂μ) ∧
    (∀ᵐ ω ∂P,
      Integrable (F ω) (NX ω) ∧
      Integrable (fun p => F ω p * F ω p) (NX ω) ∧
      Tendsto (fun n : ℕ =>
        ∫ p, (AT n).indicator (F ω) p ∂(NX ω)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ =>
        ∫ p, (AT n).indicator (fun p => |F ω p|) p ∂(NX ω))
        atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ =>
        ∫ p, (AT n).indicator (fun p => F ω p * F ω p) p ∂(NX ω))
        atTop (𝓝 0)) := by sorry
