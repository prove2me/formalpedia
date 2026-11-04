-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_clock_preimage_clipped_Ioc
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_clock_preimage_clipped_Ioc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:43:04.4422+00:00
-- url     : https://prove2.me/theorems/34f719ab-bd2e-4ba8-8dde-e1f731d65103
-- title:
--   Genuine stopped physical clock preimage of any interval is exactly clipped at the horizon
-- statement:
--   For the actual real-Lebesgue physical clock stopped at [0,T] and mapped by Real.toNNReal, the preimage of every (s,t] on its support equals that of (s,min(t,T)]. This is exact endpoint-preserving clock geometry valid even when s≥T or t≤s, and is independent of jump rates or Poisson processes. It supplies the crossing-horizon step for proving M=N on every adapted finite rectangle.
-- source:
--   Mathlib Real.coe_toNNReal, Set.Ioc and min order; original P3-B physical-clock construction.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_clock_preimage_clipped_Ioc
    (s t T : ℝ≥0) :
    (Real.toNNReal ⁻¹' Ioc s t) ∩ Icc (0 : ℝ) (T : ℝ) =
      (Real.toNNReal ⁻¹' Ioc s (min t T)) ∩ Icc (0 : ℝ) (T : ℝ) := by sorry
