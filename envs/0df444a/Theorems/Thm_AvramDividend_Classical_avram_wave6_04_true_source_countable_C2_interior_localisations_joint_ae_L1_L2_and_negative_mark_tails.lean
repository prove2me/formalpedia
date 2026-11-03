-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_countable_C2_interior_localisations_joint_ae_L1_L2_and_negative_mark_tails
-- name    : AvramDividend.Classical.avram_wave6_04_true_source_countable_C2_interior_localisations_joint_ae_L1_L2_and_negative_mark_tails
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:43:32.633205+00:00
-- url     : https://prove2.me/theorems/35b55dde-6dce-4c63-a9ab-af177cb831f7
-- title:
--   One common a.s. source jump L1 L2 and signed absolute quadratic tails for every countable C2 interior localisation
-- statement:
--   For any countable family of valid interior C2 bands (u_j+δ_j,v_j), on the original SpectrallyNegativeLevy X.X jump marks and original inclusive ruinTime, there is one common P-full event on which the prepayment stopped discounted Taylor source-count integrals are L1 and L2 and all measurable decreasing mark cutoffs have vanishing signed, absolute and squared integrals simultaneously for every j. This is a countable almost-sure quantifier upgrade of the accepted true source C2 theorem under exactly the same explicit hFuture source rectangle and hμclock physical source clock hypotheses, without postulating any new martingale isometry.
-- source:
--   Wave6 Chat04 countable localisation ae_all_iff from accepted source-specific C2 compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_randomstop_true_source_full_C2_negative_jump_pathwise_L1_L2_and_cutoff_tails

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_true_source_countable_C2_interior_localisations_joint_ae_L1_L2_and_negative_mark_tails
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ) (u v δ : ℕ → ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : ∀ j, 0 < u j) (hδ : ∀ j, 0 < δ j)
    (hδone : ∀ j, δ j ≤ 1)
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
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕.rightCont τ)
    (q : ℝ) (hq : 0 ≤ q)
    (A : ℕ → Set ℝ) (hAm : ∀ n, MeasurableSet (A n))
    (hAanti : Antitone A) (hAempty : (⋂ n, A n) = ∅),
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0) *
      (if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0)
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let J : ℕ → ((ℝ≥0 × Ω) × ℝ) → ℝ := fun j p =>
      (if Y p.1 ∈ Icc (u j + δ j) (v j) then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u j + δ j) (v j) then deriv w (Y p.1) else 0)
        else 0)
    let HS : ℕ → ((ℝ≥0 × Ω) × ℝ) → ℝ := fun j p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * J j p
    let GW : ℕ → ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      fun j p => a p.1 * HS j p
    let AT : ℕ → Set (ℝ≥0 × ℝ) := fun n => {p | p.2 ∈ A n}
    let F : ℕ → Ω → (ℝ≥0 × ℝ) → ℝ :=
      fun j ω p => GW j ((p.1, ω), p.2)
    ∀ᵐ ω ∂P, ∀ j : ℕ,
      Integrable (F j ω) (NX ω) ∧
      Integrable (fun p => F j ω p * F j ω p) (NX ω) ∧
      Tendsto (fun n : ℕ =>
        ∫ p, (AT n).indicator (F j ω) p ∂(NX ω)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ =>
        ∫ p, (AT n).indicator (fun p => |F j ω p|) p ∂(NX ω))
        atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ =>
        ∫ p, (AT n).indicator (fun p => F j ω p * F j ω p) p ∂(NX ω))
        atTop (𝓝 0) := by sorry
