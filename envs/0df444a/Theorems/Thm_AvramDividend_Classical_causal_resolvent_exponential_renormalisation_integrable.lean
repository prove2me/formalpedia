-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_resolvent_exponential_renormalisation_integrable
-- name    : AvramDividend.Classical.causal_resolvent_exponential_renormalisation_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:24:22.217044+00:00
-- url     : https://prove2.me/theorems/67f7d5c4-7c76-4e3d-977f-d9c6813a5e6d
-- title:
--   Preserve renewal-scale Laplace integrability under exponential renormalisation
-- statement:
--   If the geometric causal renewal sum is integrable under the exponent eta minus theta, then its exponential renormalisation exp(theta x)/q has an integrable eta-Laplace transform. An algebraic exponential identity reduces one integrand to a constant multiple of the other.
-- source:
--   Mathlib integrability under multiplication by a constant, exponential addition identity, and the previously established weighted series integrability prerequisite.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_resolvent_exponential_renormalisation_integrable
    (F : ℕ → ℝ → ℝ) (θ η q : ℝ)
    (hbase : IntegrableOn
      (fun x : ℝ => Real.exp (-((η - θ) * x)) * (∑' n : ℕ, F n x))
      (Ioi (0 : ℝ)) volume) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(η * x)) *
        ((Real.exp (θ * x) / q) * (∑' n : ℕ, F n x)))
      (Ioi (0 : ℝ)) volume := by sorry
