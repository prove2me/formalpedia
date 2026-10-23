-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_full_kernel_local_integrable
-- name    : AvramDividend.Classical.causal_l1_full_kernel_local_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T19:36:29.619975+00:00
-- url     : https://prove2.me/theorems/2a1f7e23-4ebd-4132-9738-00988db18b84
-- title:
--   Adding constant drift gives locally integrable causal Volterra kernel
-- statement:
--   If K is integrable on (0,∞) and β is any real drift coefficient, the complete real causal Volterra kernel β+K is integrable over every finite interval (0,R], including degenerate R≤0 (empty interval). Use finite Lebesgue measure of Ioc(0,R) for the constant integrand and restrict K's positive-axis L1 property to the subset Ioc(0,R). This is a fully reusable local kernel bound for Volterra existence, Fubini and uniqueness.
-- source:
--   MeasureTheory.IntegrableOn.mono_set; integrableOn_const; measure_Ioc_lt_top

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_l1_full_kernel_local_integrable
    (K : ℝ → ℝ) (β R : ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun t : ℝ => β + K t) (Ioc (0 : ℝ) R) volume := by sorry
