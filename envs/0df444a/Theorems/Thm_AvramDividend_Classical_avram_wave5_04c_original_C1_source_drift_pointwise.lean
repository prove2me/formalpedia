-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_original_C1_source_drift_pointwise
-- name    : AvramDividend.Classical.avram_wave5_04c_original_C1_source_drift_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:35:50.057924+00:00
-- url     : https://prove2.me/theorems/2a10ce58-ac31-4408-b83e-2c6797f1ad5c
-- title:
--   Original Lévy source pathwise C1 physical-drift first-order shift limit
-- statement:
--   For each exact original source sample path ω, the physical drift shift h↦w(x+X_h(ω))-w(x+X_h(ω)-d h) divided by h tends to d w'(x) as h↓0, using Real.toNNReal h. This follows from genuine right continuity of X at zero, X_0=0, and the Proved C1 moving-base strict secant theorem. No assumption on the jump process beyond the original source structure and no replacement process.
-- source:
--   Remotely compiled source to be submitted candidates/work_on/AvramDividend_04c_original_C1_BV_drift_pointwise_shift_probe.lean; SHA256 455f28391b43fedd5c6cae98b3bc96250ba09f684b06bd61a7f7ced597285f85

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_moving_base_drift_secant
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_original_C1_source_drift_pointwise {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (x d : ℝ) (ω : Ω) :
    Tendsto (fun h : ℝ => h⁻¹ *
        (w (x + X.X (Real.toNNReal h) ω) -
         w (x + X.X (Real.toNNReal h) ω - d * h)))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (d * deriv w x)) := by sorry
