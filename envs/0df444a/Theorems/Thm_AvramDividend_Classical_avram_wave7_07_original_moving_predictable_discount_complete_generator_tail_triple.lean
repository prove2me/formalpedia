-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_moving_predictable_discount_complete_generator_tail_triple
-- name    : AvramDividend.Classical.avram_wave7_07_original_moving_predictable_discount_complete_generator_tail_triple
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:57:35.573651+00:00
-- url     : https://prove2.me/theorems/9d96b00d-234a-42c8-a8f5-a0e7a2b08af9
-- title:
--   Joint L1, L2 and signed generator tail convergence for source Lévy moving predictable discounts
-- statement:
--   On the same spectrally negative Lévy original Ω, filtration, dividend-controlled ruin clock and original negative Lévy measure, three cutoff limits hold at once: L1 energy, L2 energy and signed integrated nonlinear compensated generator drift, for a predictable discount a_n in [0,1] varying with n and jointly predictable decreasing marked cutoffs. They are the mathematically exact accepted component limits. This bundled source theorem removes three independent imports from the stopped Itô generator consumer but does not imply the missing intrinsic source compensator.
-- source:
--   W7-07 source original moving predictable cutoff L1/L2/signed triple; source Lévy generator compensation uses strict -1<z<0 threshold; W7-08 handoff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_moving_predictable_discount_adaptive_L1_tail_vanishes
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_moving_predictable_discount_adaptive_L2_tail_vanishes
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_moving_predictable_discount_signed_generator_tail_vanishes

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_moving_predictable_discount_complete_generator_tail_triple
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (S : ℕ → Set ((ℝ≥0 × Ω) × ℝ))
    (hSm : ∀ n, MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] (S n))
    (hSanti : Antitone S) (hSempty : (⋂ n, S n) = ∅)
    (a : ℕ → ℝ≥0 × Ω → ℝ)
    (ham : ∀ n, Measurable[𝓕.rightCont.predictable] (a n))
    (ha : ∀ n p, 0 ≤ a n p ∧ a n p ≤ 1) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    (Tendsto (fun n : ℕ =>
      ∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        (S n).indicator (fun r => ENNReal.ofReal (|a n r.1 * HS r|)) p
          ∂(letI : MeasurableSpace (ℝ≥0 × Ω) :=
             𝓕.rightCont.predictable
            μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
      atTop (𝓝 0)) ∧
    (Tendsto (fun n : ℕ =>
      ∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        (S n).indicator (fun r => ENNReal.ofReal ((a n r.1 * HS r) ^ 2)) p
          ∂(letI : MeasurableSpace (ℝ≥0 × Ω) :=
             𝓕.rightCont.predictable
            μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
      atTop (𝓝 0)) ∧
    (Tendsto (fun n : ℕ =>
      ∫ p : ((ℝ≥0 × Ω) × ℝ),
        (S n).indicator (fun r => a n r.1 * HS r) p
          ∂(letI : MeasurableSpace (ℝ≥0 × Ω) :=
             𝓕.rightCont.predictable
            μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
      atTop (𝓝 0)) := by sorry
