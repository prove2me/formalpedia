-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_moving_predictable_discount_adaptive_L1_tail_vanishes
-- name    : AvramDividend.Classical.avram_wave7_07_original_moving_predictable_discount_adaptive_L1_tail_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:37:44.950731+00:00
-- url     : https://prove2.me/theorems/55f5b726-25eb-456f-aa2a-d4093e6d097f
-- title:
--   Original Lévy stopped nonlinear Taylor L1 tails vanish even with time-state-dependent predictable discount changing at each cutoff
-- statement:
--   For the actual spectrally negative Lévy source, original dividend strategy and ruin-stopped nonlinear C2 negative-jump generator correction, allow arbitrary measurable decreasing predictable marked cutoffs S_n with empty intersection and a different predictable discount a_n∈[0,1] at every n. The absolute L1 product energy against the genuine μ⊗X.ν negative-mark clock still vanishes. This uniform contraction follows from the proved adaptive full-weight L1 tail and an ENNReal squeeze. It permits moving finite-horizon stochastic localisation and retains the source truncation convention.
-- source:
--   W7-07 original source uniform moving predictable discount contraction from proved adaptive L1 source 89c82c95, with an ENNReal order-topology squeeze; precise approximation theorem for W7-06/W7-08.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_bounded_predictable_discount_thinned_taylor_L1_L2_energy
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_moving_predictable_discount_adaptive_L1_tail_vanishes
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
    Tendsto (fun n : ℕ =>
      ∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        (S n).indicator (fun r =>
          ENNReal.ofReal (|a n r.1 * HS r|)) p
          ∂(letI : MeasurableSpace (ℝ≥0 × Ω) :=
             𝓕.rightCont.predictable
            μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
      atTop (𝓝 0) := by sorry
