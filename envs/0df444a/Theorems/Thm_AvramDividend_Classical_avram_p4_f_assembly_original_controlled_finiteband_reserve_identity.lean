-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_controlled_finiteband_reserve_identity
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_controlled_finiteband_reserve_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:16:01.56901+00:00
-- url     : https://prove2.me/theorems/e9bcd24b-7bb8-45e2-9031-29f509a64072
-- title:
--   Exact original controlled reserve finite negative jump band decomposition
-- statement:
--   For the actual spectrally negative Levy path X and dividend strategy D, express the genuine prepayment reserve at every finite time as original drift, an intrinsic compensated strictly-small negative finite jump band, original large-jump sum, and the exact remaining source residual, subtracting original D. The small band excludes z=-1 and the large band includes z=-1. This is a pathwise source decomposition, without claiming a martingale property or stopped Itô identity.
-- source:
--   Proved P4-H original intrinsic source-jump-series theorem 7c80f340-cc1f-4197-bf5d-c4240aff927d and original dividend riskProcess definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_truncated_residual_source_jump_series
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_controlled_finiteband_reserve_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let E : Set (ℝ≥0 × ℝ) :=
      Ioc (0 : ℝ≥0) t ×ˢ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
    riskProcess X x D t ω =
      x + (t : ℝ) * X.c +
        ((∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then
            E.indicator (fun p : ℝ≥0 × ℝ => p.2) (u, j u) else 0) -
          (t : ℝ) * (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)) +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
        D t ω := by sorry
