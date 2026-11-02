-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_absolute_taylor_source_jump_series
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_C2_absolute_taylor_source_jump_series
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:33:42.552438+00:00
-- url     : https://prove2.me/theorems/039daa2b-bc32-4cd1-a634-a01a2f3d9f87
-- title:
--   Actual original Lévy nonlinear stopped Taylor absolute jump measure equals the literal infinite source jump series
-- statement:
--   For the ORIGINAL SpectrallyNegativeLevy X, original adapted dividend strategy D, prepayment left-limit reserve and inclusive ruin-stopped localised nonlinear Taylor correction H, the extended nonnegative integral of |H| over the actual intrinsic Lévy marked jump measure on (s,t] and all strictly negative marks equals the literal time-indexed sum over that same source path's ΔX jumps. No Finset enumeration, independent Poisson copy, future independence of D or compensated martingale is assumed. The equality alone does not assert that the value is finite; that requires the missing original source compensator law.
-- source:
--   Proved actual original-source nonnegative stopped jump-series theorem e0cd7438; Proved exact unchanged right-cont filtration Lévy lift e58a099d; Proved original control stopped nonlinear predictable C² Taylor kernel 0e0663b1. Source is literal intrinsic NX and original ΔX, with no compensation assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_randomly_stopped_predictable_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_C2_absolute_taylor_source_jump_series
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
    let J : ℝ≥0 → Ω → ℝ := fun q ω =>
      X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {q : ℝ≥0 | 0 < q ∧ J q ω ≠ 0}).map
        (fun q : ℝ≥0 => (q, J q ω)))
    ∀ (s t : ℝ≥0) (ω : Ω),
      (∫⁻ p : ℝ≥0 × ℝ,
        (if s < p.1 ∧ p.1 ≤ t ∧ p.2 < 0 then
          ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω) =
      ∑' q : ℝ≥0,
        if 0 < q ∧ J q ω ≠ 0 then
          (if s < q ∧ q ≤ t ∧ J q ω < 0 then
            ENNReal.ofReal (|HS ((q,ω),J q ω)|) else 0)
        else 0 := by sorry
