-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_levy_absolute_first_moment
-- name    : AvramDividend.Classical.avram_gen14_singular_levy_absolute_first_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:48:05.373204+00:00
-- url     : https://prove2.me/theorems/d3082df7-861a-40db-baf3-aae092250724
-- title:
--   Proposed singular negative Levy jump measure has first absolute moment two
-- statement:
--   The first absolute jump moment of the proposed spectrally negative Levy measure, defined by the inverse-three-halves density on negative jumps of magnitude below one, evaluates to two. This is a concrete finite-variation moment identity needed to construct a genuine standing Levy process and bound its expected downward variation.
-- source:
--   Accepted density-restriction integral and pinned intervalIntegral.integral_comp_neg and integral_rpow, with exact inverse-square-root integration from zero to one.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gen14_singular_levy_absolute_first_moment :
    (∫ z : ℝ, |z| ∂(volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))) = 2 := by sorry
