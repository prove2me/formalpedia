-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_jump_and_pathwise_compensator_separate_L1_equal_means
-- name    : AvramDividend.Classical.avram_wave6_02_actual_discounted_ruin_stopped_Taylor_jump_and_pathwise_compensator_separate_L1_equal_means
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:56:49.451497+00:00
-- url     : https://prove2.me/theorems/ee54a24a-9b62-4406-bf84-8e059ae100d3
-- title:
--   Original ruin-stopped C² Taylor jump sum and its random sample-wise Lévy compensator are separately L¹ with exactly equal expectations
-- statement:
--   Strengthens the actual controlled original-source discounted and inclusive ruin-stopped Taylor compensation theorem: independently prove the original jump count integral and the random sample-wise predictable mark-fibre time compensator are both Bochner integrable against P, and their expectations are equal. Genuine original X, controlled surplus and 𝓕.rightCont predictability, with the exact hFuture marked rectangle law and finite original νnegative mark bands. Explicitly no small-jump first absolute moment assumption; signed original physical-clock fibre Fubini and the original source compensated mean-zero lemma are reused.
-- source:
--   Reuse original signed actual physical-clock predictable fibre Fubini for hCompInt and hCompMean, original discounted stopped centred sum for hJumpInt and hJumpMean; conclude equality of the two separately integrable means.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_predictable_signed_mark_compensator_fibre_Fubini
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_true_clock_initial_future_rectangles_force_finite_mark_band
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_controlled_stopped_Taylor_jump_L1_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_bounded_predictable_weight_source_product_generator_drift_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_actual_discounted_ruin_stopped_Taylor_jump_and_pathwise_compensator_separate_L1_equal_means
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
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
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
    ∀ (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hST : S = {p | p.1.1 ≤ T})
    (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (B : ℕ → Set ℝ) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hνBand : ∀ k, (X.ν.restrict (Iio (0 : ℝ))) (B k) < ⊤)
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕.rightCont i] A → MeasurableSet C →
      MT ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C))
    (q : ℝ) (hq : 0 ≤ q),
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
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
    let η : Measure ℝ≥0 := (((volume : Measure ℝ).restrict
      (Icc 0 (T : ℝ))).map Real.toNNReal)
    let Comp : Ω → ℝ := fun ω =>
      ∫ t, ∫ z, GW ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂η
    let Jump : Ω → ℝ := fun ω =>
      ∫ p, GW ((p.1, ω), p.2) ∂(NX ω)
    Integrable Jump P ∧ Integrable Comp P ∧
    (∫ ω, Jump ω ∂P) = (∫ ω, Comp ω ∂P))  := by sorry
