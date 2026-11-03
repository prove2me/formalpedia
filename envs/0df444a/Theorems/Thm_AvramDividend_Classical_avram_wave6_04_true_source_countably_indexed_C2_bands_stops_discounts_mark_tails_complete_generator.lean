-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_countably_indexed_C2_bands_stops_discounts_mark_tails_complete_generator
-- name    : AvramDividend.Classical.avram_wave6_04_true_source_countably_indexed_C2_bands_stops_discounts_mark_tails_complete_generator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:58:01.545525+00:00
-- url     : https://prove2.me/theorems/3d3b753b-63a7-4113-9274-408b09b4fbd2
-- title:
--   Actual source nonlinear C2 generator and simultaneous negative tails for arbitrary countable bands, stops, discount rates and cutoff schedules
-- statement:
--   Across any countable index type, actual source jumps, prepayment left limits and ruinTime admit per-index stopped discounted C2 generator compensation against X.ν and a common almost-sure event of L1/L2 and negative-mark tail convergence. Bands, source stopping times, nonnegative discounts and antitone negative-mark cutoff schedules may all vary by index under explicit exact source rectangle intensity and clock hypotheses.
-- source:
--   Wave6 Chat04 original source countably-indexed theorem via accepted single-index compensation and ae_all_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_randomstop_true_source_complete_C2_generator_compensation_and_pathwise_negative_tails

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_true_source_countably_indexed_C2_bands_stops_discounts_mark_tails_complete_generator
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
    let AT : ι → ℕ → Set (ℝ≥0 × ℝ) := fun j n => {p | p.2 ∈ A j n}
    let F : ι → Ω → (ℝ≥0 × ℝ) → ℝ := fun j ω p => GW j ((p.1, ω), p.2)
    (∀ j : ι,
      Integrable (fun ω =>
      ∫ p, GW j ((p.1, ω), p.2) ∂(NX ω)) P ∧
    (∫ ω, (∫ p, GW j ((p.1, ω), p.2) ∂(NX ω)) ∂P) =
      (∫ p : ℝ≥0 × Ω,
        a j p * (∫ z in Iio (0 : ℝ), JG j (p, z) ∂X.ν) ∂μ)) ∧
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
