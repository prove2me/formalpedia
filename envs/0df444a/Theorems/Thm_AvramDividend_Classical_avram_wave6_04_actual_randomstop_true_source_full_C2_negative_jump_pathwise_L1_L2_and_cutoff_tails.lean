-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_randomstop_true_source_full_C2_negative_jump_pathwise_L1_L2_and_cutoff_tails
-- name    : AvramDividend.Classical.avram_wave6_04_actual_randomstop_true_source_full_C2_negative_jump_pathwise_L1_L2_and_cutoff_tails
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:18:10.459036+00:00
-- url     : https://prove2.me/theorems/a9a0325d-8662-4fa3-9472-951987414b93
-- title:
--   Original randomly stopped C2 source negative-jump L1, L2 and all mark-cutoff tails
-- statement:
--   A consolidated original-source compensated negative-jump C2 interface for the stopped discounted generator assembly: under explicitly stated true physical hμclock, rightCont future-rectangle hFuture, finite mark bands and actual jump count, the source Taylor kernel is almost surely absolutely and quadratically integrable on NX(ω), while its signed, absolute and quadratic integrals along every decreasing measurable mark tail converge to zero. It uses literal prepayment Y-, original ruinTime, and SpectrallyNegativeLevy.generatorIntegrand truncation. It is independent of Chat02 jump martingale isometry, Chat03 Gaussian bracket and Chat05 dividend jumps; no generic clock compensator is inferred.
-- source:
--   Wave6 Chat04 final compact Chat06 consumer theorem assembled from accepted source C2 L1/L2 and pathwise mark-cutoff DCT components. Declaration-only preamble omits a proof-only Open dependency; the proof source retains its full import and is submitted only once that dependency is Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_randomstop_discounted_C2_negative_jump_pathwise_L1_from_true_source_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_randomstop_discounted_C2_negative_jump_pathwise_quadratic_energy_from_true_source_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_integrable_signed_measurable_antitone_set_tails_tendsto_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_randomstop_true_source_full_C2_negative_jump_pathwise_L1_L2_and_cutoff_tails
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
    let AT : ℕ → Set (ℝ≥0 × ℝ) := fun n => {p | p.2 ∈ A n}
    let F : Ω → (ℝ≥0 × ℝ) → ℝ := fun ω p => GW ((p.1, ω), p.2)
    ∀ᵐ ω ∂P,
      Integrable (F ω) (NX ω) ∧
      Integrable (fun p => F ω p * F ω p) (NX ω) ∧
      Tendsto (fun n : ℕ =>
        ∫ p, (AT n).indicator (F ω) p ∂(NX ω)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ =>
        ∫ p, (AT n).indicator (fun p => |F ω p|) p ∂(NX ω))
        atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ =>
        ∫ p, (AT n).indicator (fun p => F ω p * F ω p) p ∂(NX ω))
        atTop (𝓝 0) := by sorry
