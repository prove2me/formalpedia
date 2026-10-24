-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_positive_L1_intervalIntegrable
-- name    : AvramDividend.Classical.causal_positive_L1_intervalIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T10:54:17.617611+00:00
-- url     : https://prove2.me/theorems/83d224a1-0b2c-4ef5-81a0-e528c439f963
-- title:
--   Global positive-time L1 integrability implies finite-interval integrability
-- statement:
--   An L1 kernel on strictly positive times is interval-integrable from zero to every finite strictly positive endpoint; the value at zero is irrelevant to Lebesgue integration.
-- source:
--   Narrow bridge from the Volterra kernel L1 hypothesis to FTC hypotheses for positive-time primitives.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory Set

theorem AvramDividend.Classical.causal_positive_L1_intervalIntegrable
    (K : ℝ → ℝ) (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (x : ℝ) (hx : 0 < x) :
    IntervalIntegrable K volume 0 x := by sorry
