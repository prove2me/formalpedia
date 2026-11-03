-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_countable_C2_generator_physical_time_compensation_joint_ae_tails
-- name    : AvramDividend.Classical.avram_wave6_04_true_source_countable_C2_generator_physical_time_compensation_joint_ae_tails
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:01:09.013363+00:00
-- url     : https://prove2.me/theorems/719b2897-6e60-4bd8-b339-32f9985999d7
-- title:
--   Countable source C2 interior bands and randomstops: physical-time generator compensation with common AE negative tails
-- statement:
--   For every countable family of interior C2 localisations, genuine source right-continuous stopping times, discounts and antitone negative-mark cutoff schedules, prove the literal X.X stopped nonlinear jump-Taylor sum integrable with expectation equal to the true physical-time × P integral of the source negative X.ν generatorIntegrand, and one common almost-sure event controlling all L1/L2 source jump-count tails. The actual source future-rectangle intensity hFuture remains an explicit Chat01 hypothesis, and each generator drift need only be AE strongly predictable. Avoid generic compensator clock assumptions.
-- source:
--   Wave6 Chat04 original countable localisation theorem and independently Accepted AE physical generator time transport, source X.X and true X.ν.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_randomstop_true_source_complete_C2_generator_compensation_and_pathwise_negative_tails
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_stopped_discounted_negative_generator_ae_physical_time_integral_transport

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_true_source_countable_C2_generator_physical_time_compensation_joint_ae_tails
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ι : Type*} [Countable ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ) (u v δ : ι → ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : ∀ j, 0 < u j) (hδ : ∀ j, 0 < δ j) (hδone : ∀ j, δ j ≤ 1)
    (huv : ∀ j, u j + δ j < v j) (hv : ∀ j, v j < C)
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
    (τ : ι → Ω → ℝ≥0∞)
    (hτ : ∀ j : ι, IsStoppingTime 𝓕.rightCont (τ j))
    (q : ι → ℝ) (hq : ∀ j : ι, 0 ≤ q j)
    (A : ι → ℕ → Set ℝ) (hAm : ∀ j n, MeasurableSet (A j n))
    (hAneg : ∀ j n, A j n ⊆ Iio (0 : ℝ))
    (hAanti : ∀ j, Antitone (A j)) (hAempty : ∀ j, (⋂ n, A j n) = ∅),
    let a : ι → (ℝ≥0 × Ω) → ℝ := fun j p =>
      (if p.1 ≤ T then Real.exp (-(q j * (p.1 : ℝ))) else 0) *
      (if (p.1 : ℝ≥0∞) ≤ τ j p.2 then (1 : ℝ) else 0)
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let J : ι → ((ℝ≥0 × Ω) × ℝ) → ℝ := fun j p =>
      (if Y p.1 ∈ Icc (u j + δ j) (v j) then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u j + δ j) (v j) then deriv w (Y p.1) else 0)
        else 0)
    let HS : ι → ((ℝ≥0 × Ω) × ℝ) → ℝ := fun j p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * J j p
    let GW : ι → ((ℝ≥0 × Ω) × ℝ) → ℝ := fun j p => a j p.1 * HS j p
    let JG : ι → ((ℝ≥0 × Ω) × ℝ) → ℝ := fun j p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u j + δ j) (v j) then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    (∀ j : ι,
      AEStronglyMeasurable[𝓕.rightCont.predictable]
        (fun p : ℝ≥0 × Ω =>
          a j p * (∫ z in Iio (0 : ℝ), JG j (p, z) ∂X.ν)) μ) →
    let AT : ι → ℕ → Set (ℝ≥0 × ℝ) := fun j n => {p | p.2 ∈ A j n}
    let F : ι → Ω → (ℝ≥0 × ℝ) → ℝ := fun j ω p => GW j ((p.1, ω), p.2)
    (∀ j : ι,
      Integrable (fun ω =>
      ∫ p, GW j ((p.1, ω), p.2) ∂(NX ω)) P ∧
    (∫ ω, (∫ p, GW j ((p.1, ω), p.2) ∂(NX ω)) ∂P) =
      (∫ p : ℝ≥0 × Ω,
        a j p * (∫ z in Iio (0 : ℝ), JG j (p, z) ∂X.ν)
        ∂((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P))) ∧
    (∀ᵐ ω ∂P, ∀ j : ι,
      Integrable (F j ω) (NX ω) ∧
      Integrable (fun p => F j ω p * F j ω p) (NX ω) ∧
      Tendsto (fun n : ℕ =>
        ∫ p, (AT j n).indicator (F j ω) p ∂(NX ω)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ =>
        ∫ p, (AT j n).indicator (fun p => |F j ω p|) p ∂(NX ω))
        atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ =>
        ∫ p, (AT j n).indicator (fun p => F j ω p * F j ω p) p ∂(NX ω))
        atTop (𝓝 0)) := by sorry
