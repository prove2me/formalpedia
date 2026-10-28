-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_damped_positive_L1_intervalIntegrable
-- name    : AvramDividend.Classical.causal_damped_positive_L1_intervalIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T17:13:26.539298+00:00
-- url     : https://prove2.me/theorems/8ef01657-7302-499e-a0a5-da322a001ff8
-- title:
--   Exponentially damped causal L1 kernels are interval-integrable
-- statement:
--   For every positive endpoint x, an L1 kernel on positive times remains interval-integrable after multiplication by the exponential time-lag factor exp(-w(x-s)). This discharges the weighted primitive integrability hypothesis in the Gaussian Neumann-series mass and derivative estimates.
-- source:
--   First restrict the positive-time L1 kernel to the finite interval using causal_positive_L1_intervalIntegrable. The multiplicative damping s↦exp(-w(x-s)) is continuous on the compact interval. Apply the exact pinned IntervalIntegrable.continuousOn_mul theorem, whose arguments are the L1 proof and the damping continuity proof.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_causal_positive_L1_intervalIntegrable

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_damped_positive_L1_intervalIntegrable
    (P : ℝ → ℝ) (w x : ℝ)
    (hP : IntegrableOn P (Ioi (0 : ℝ)) volume)
    (hx : 0 < x) :
    IntervalIntegrable
      (fun s : ℝ => Real.exp (-w * (x - s)) * P s)
      volume 0 x := by sorry
