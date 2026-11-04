-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_restriction_bound
-- name    : AvramDividend.Classical.avram_p2_j_ui_l2_restriction_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:19:23.952327+00:00
-- url     : https://prove2.me/theorems/3a456579-f8a7-4e0f-b5e6-0d8779886dba
-- title:
--   Uniform L² envelope controls the L¹ seminorm on every measurable restriction
-- statement:
--   For every real-valued almost-everywhere strongly measurable function with a finite bound B on its L2 seminorm, its L1 seminorm on any restricted measure is bounded by B times the square root of that set's measure. This is the quantitative Cauchy-Schwarz modulus needed to turn a uniform second-moment estimate into uniform integrability, with no Lévy-specific input.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_l2_restriction_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (B : ℝ≥0)
    (hm : AEStronglyMeasurable Y P)
    (hB : eLpNorm Y 2 P ≤ (B : ENNReal))
    (s : Set Ω) :
    eLpNorm Y 1 (P.restrict s) ≤
      (B : ENNReal) * (P s) ^ (1 / 2 : ℝ) := by sorry
