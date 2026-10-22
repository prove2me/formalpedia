-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_negative_mark_interval_reflect
-- name    : AvramDividend.Classical.chat06_negative_mark_interval_reflect
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:57:16.962609+00:00
-- url     : https://prove2.me/theorems/a274f1a6-5e55-44ee-978e-832cedb89454
-- title:
--   Reflection of the downward-jump exponential integral to positive claim sizes
-- statement:
--   Reflecting a uniform downward-jump interval (-2,-1) to the corresponding positive claim interval (1,2) maps the exponential moment integral to its negative-exponent form. The Jacobian has absolute value one, so no scale factor is introduced. This identifies the downward-jump Lévy exponent with the positive claim-size Laplace transform.
-- source:
--   Existing source bv_negative_uniform_mark_interval_reflection_chat06_20261020.lean, 32 lines, 976 bytes, SHA-256 291acb4d7691598cd03d7a49a00d223f977c6690cfc69e89e65e60bb132c1297. Private remote probe 3bc46fec-7121-4830-999d-492523cecde4 reached sentinel with zero source errors.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring

open Real MeasureTheory

theorem AvramDividend.Classical.chat06_negative_mark_interval_reflect (θ : ℝ) :
    (∫ y in (-2 : ℝ)..(-1 : ℝ), Real.exp (θ * y)) =
      ∫ x in (1 : ℝ)..2, Real.exp (-(θ * x)) := by sorry
