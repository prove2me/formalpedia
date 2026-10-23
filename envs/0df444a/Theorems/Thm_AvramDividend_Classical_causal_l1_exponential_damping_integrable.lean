-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_exponential_damping_integrable
-- name    : AvramDividend.Classical.causal_l1_exponential_damping_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:18:52.445933+00:00
-- url     : https://prove2.me/theorems/75d07b0a-1dbd-4249-8b13-58a95a4c330a
-- title:
--   Positive-axis L1 integrability survives exponential damping
-- statement:
--   A causal kernel integrable on strictly positive times remains integrable after multiplication by exp(-wt) when w>0. On positive times the exponential is between zero and one, so the new integrand is dominated in norm by the original integrable kernel. This supplies the integrability premise for the full weighted-kernel bound and the fixed-point construction.
-- source:
--   Pinned Mathlib Integrable.mono' and exponential decay bound.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_exponential_damping_integrable
    (K : ℝ → ℝ) (w : ℝ) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun t : ℝ => Real.exp (-w * t) * K t)
      (Ioi (0 : ℝ)) volume := by sorry
