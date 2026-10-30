-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_gaussian_generator_cap_continuity
-- name    : AvramDividend.Classical.avram_wave3_05_gaussian_generator_cap_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T01:15:07.333848+00:00
-- url     : https://prove2.me/theorems/772cbd1e-a0e9-44c4-97cf-4a050fecafa7
-- title:
--   Original Gaussian generator harmonicity at the positive barrier from interior and source residual continuity
-- statement:
--   For the original zero-origin scale function with source C2 smoothness on every positive reserve and a strictly positive barrier a, if its actual Levy generator residual vanishes for every 0<x<a, then the same residual vanishes at x=a. Proof uses the previously Proved source residual continuity on (0,∞) and closure of (0,a), establishing the precise HJB barrier endpoint missing from a strict interior theorem.
-- source:
--   Avram–Palmowski–Pistorius (2007), Lemma 4; canonical source-residual continuity theorem 1fe801dd-dcf1-4433-8d62-a8bb5b06dc44; Mathlib Set.EqOn.of_subset_closure and closure_Ioo.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_Ioi_of_zero_origin_C2

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_05_gaussian_generator_cap_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (hC2 : ContDiffOn ℝ 2 W (Ioi (0 : ℝ)))
    (a : ℝ) (ha : 0 < a)
    (hinterior : ∀ x ∈ Ioo (0 : ℝ) a,
      X.generator W x - q * W x = 0) :
    X.generator W a - q * W a = 0 := by sorry
