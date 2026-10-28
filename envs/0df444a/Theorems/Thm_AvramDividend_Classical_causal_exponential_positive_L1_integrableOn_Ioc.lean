-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_exponential_positive_L1_integrableOn_Ioc
-- name    : AvramDividend.Classical.causal_exponential_positive_L1_integrableOn_Ioc
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:30:59.642993+00:00
-- url     : https://prove2.me/theorems/5c085f24-de06-415b-8d1c-83f8b6ad1b36
-- title:
--   Exponential untilting preserves finite-horizon L1 integrability
-- statement:
--   A kernel integrable on all positive times remains integrable on every finite positive horizon when multiplied by exp(w s), for any real exponent w. Supplies the exact two weighted-local-L1 hypotheses of the Gaussian signed Neumann primitive recurrence.
-- source:
--   Reuse the canonical proof of causal_damped_positive_L1_intervalIntegrable: restrict the positive-time L1 input to compact [0,x], use continuity of exp(w s) and IntegrableOn.continuousOn_mul, then pass to the endpoint-equivalent interval (0,x].

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FunProp

open MeasureTheory Set

theorem AvramDividend.Classical.causal_exponential_positive_L1_integrableOn_Ioc
    (P : ℝ → ℝ) (w x : ℝ)
    (hP : IntegrableOn P (Ioi (0 : ℝ)) volume)
    (hx : 0 < x) :
    IntegrableOn (fun s : ℝ => Real.exp (w * s) * P s)
      (Ioc (0 : ℝ) x) volume := by sorry
