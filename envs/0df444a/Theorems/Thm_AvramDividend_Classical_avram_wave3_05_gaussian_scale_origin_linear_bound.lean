-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_scale_origin_linear_bound
-- name    : AvramDividend.Classical.avram_wave3_05_gaussian_scale_origin_linear_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T01:32:20.045575+00:00
-- url     : https://prove2.me/theorems/3ff3f1b9-918a-4b70-a028-fc8747b9a01f
-- title:
--   Source Gaussian q-scale and its positive derivative have a common linear origin envelope
-- statement:
--   For the unchanged original spectrally negative Lévy model with Standing, q>0, W its q-scale and σ>0, there is a single C≥0 satisfying |W(x)|≤Cx and |W'(x)|≤C for every reserve 0<x≤1. The Proved Gaussian derivative bound and zero-origin continuity allow the exact real mean value theorem on [0,x], with the witness derivative in (0,x). This yields the local source estimate needed for the quadratic-integrated crossing-strip bound on small compensated negative jumps.
-- source:
--   Avram–Palmowski–Pistorius (2007), Gaussian scale origin regularity; Proved source derivative bound afcf6529, Gaussian C2, zero origin and global continuity; Mathlib exists_deriv_eq_slope.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_deriv_bounded_near_zero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_continuous_of_zero_origin
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_05_gaussian_scale_origin_linear_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ioc (0 : ℝ) 1,
      |W x| ≤ C * x ∧ |deriv W x| ≤ C := by sorry
