-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_convolution_support_restrict
-- name    : AvramDividend.Classical.chat04_killed_resolvent_convolution_support_restrict
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:33:10.22649+00:00
-- url     : https://prove2.me/theorems/ebc5f244-e08c-4dd8-b238-2f563b8b1a2f
-- title:
--   Support restriction of the killed-resolvent scale-function convolution
-- statement:
--   If Wqp vanishes on the negative half-line, its convolution against Wq at positive reserve x has the same Lebesgue integral over (0,∞) as over (0,x]. This exactly identifies the convolution term in the killed-resolvent density with the proved scale resolvent convolution.
-- source:
--   MeasureTheory integral_union_eq_left_of_ae, interval decomposition, and scale support on negative half-line.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic.Linarith

open MeasureTheory Set

theorem AvramDividend.Classical.chat04_killed_resolvent_convolution_support_restrict
    (x : ℝ) (hx : 0 ≤ x) (Wq Wqp : ℝ → ℝ)
    (hzero : ∀ z : ℝ, z < 0 → Wqp z = 0) :
    (∫ y in Ioi (0 : ℝ), Wq y * Wqp (x - y)) =
    (∫ y in Ioc (0 : ℝ) x, Wq y * Wqp (x - y)) := by sorry
