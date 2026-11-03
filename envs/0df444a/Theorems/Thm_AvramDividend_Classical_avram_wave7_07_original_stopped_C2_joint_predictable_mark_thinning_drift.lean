-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_stopped_C2_joint_predictable_mark_thinning_drift
-- name    : AvramDividend.Classical.avram_wave7_07_original_stopped_C2_joint_predictable_mark_thinning_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:09:58.433144+00:00
-- url     : https://prove2.me/theorems/95e71e5b-8d80-4112-822e-5de5a81c19a2
-- title:
--   Jointly predictable negative-mark thinning of the actual stopped C² source Taylor correction preserves predictable drift
-- statement:
--   On the genuine spectrally negative Lévy source, let S be any jointly predictable set of time/omega/mark points. The ruin-stopped C² compensated Taylor correction with the canonical small-negative-mark truncation, integrated against the actual restricted source Lévy measure over negative marks and thinned by S, is predictable as a function of time and omega. The result is algebraic-measure theoretic and does not assume or assert a new Poisson sample space, jump martingale, or intrinsic jump-count compensator.
-- source:
--   Wave 7 Chat 07 independent predictable-mark thinning interface to Wave6 actual C2 source Taylor kernel 0e0663b1 and sFinite negative Lévy measure a9270e22; source exact generator equality supplied by e336f7e2 where needed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_stopped_C2_joint_predictable_mark_thinning_drift
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
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hS : MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] S) :
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
    Measurable[𝓕.rightCont.predictable] (fun p : ℝ≥0 × Ω =>
      ∫ z in Iio (0 : ℝ),
        (S.indicator HS) (p,z) ∂X.ν) := by sorry
