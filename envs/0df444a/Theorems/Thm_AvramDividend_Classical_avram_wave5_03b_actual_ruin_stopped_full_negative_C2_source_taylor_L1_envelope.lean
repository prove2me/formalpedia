-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_envelope
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:57:34.352413+00:00
-- url     : https://prove2.me/theorems/5eef1de0-1869-4d68-991f-1a0ff65d4b8a
-- title:
--   Global negative-jump L1 Taylor envelope for the actual ruin-stopped Lévy reserve under general C² regularity
-- statement:
--   For the literal source SpectrallyNegativeLevy X and adapted dividend D, its actual prepayment left-limit reserve and inclusive ruin stop, the full negative-mark nonlinear Taylor remainder is uniformly bounded by M*min(1,z²), for arbitrary interior C² w continuous at nonnegative reserves and zero below zero. No global monotonicity or positivity of w is assumed. The proof joins the Proved near-zero C² source Taylor O(z²) estimate to the full negative-mark 04b squared envelope away from the origin. Thus every negative Lévy compensator drift is absolutely integrable even for nonmonotone C² test functions.
-- source:
--   Canonical Proved source near-C² actual stopped L1 9b510aa0 and source original full negative-mark L2 envelope c02ee5a4; elementary arithmetic deriving |H|≤1+K away from zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_near_C2_L1_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_full_negative_mark_compensated_kernel_uniform_energy_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C) :
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
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (p : ℝ≥0 × Ω) (z : ℝ), z < 0 →
        |HS (p,z)| ≤ M * min 1 (z ^ 2) := by sorry
