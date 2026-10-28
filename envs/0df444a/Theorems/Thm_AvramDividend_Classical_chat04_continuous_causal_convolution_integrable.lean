-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_continuous_causal_convolution_integrable
-- name    : AvramDividend.Classical.chat04_continuous_causal_convolution_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:23:44.898977+00:00
-- url     : https://prove2.me/theorems/6ee76d1b-d1c5-4e17-94ec-7b4e1a16d459
-- title:
--   Continuity and negative-half-line support imply integrability of causal scale convolution
-- statement:
--   If real functions f,g are globally continuous and g vanishes on strictly negative arguments, the causal convolution integrand y↦f(y)g(x−y) is Lebesgue-integrable over y>0 for every x. For y>x the integrand vanishes; on 0≤y≤x it is continuous on a compact interval. This independently discharges the compact convolution integrability premise in the killed q-scale resolvent analytic kernel theorem once global scale-function continuity is available.
-- source:
--   Direct compact-continuity argument; Mathlib Continuous.integrableOn_Icc and IntegrableOn.of_ae_sdiff_eq_zero. Relevant Proved target chat04_killed_resolvent_density_scale_action_of_integrable UUID 34efb710-e219-4148-a5a3-a178bce547ec. No exit identities or semigroup harmonicity.

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory Set

theorem AvramDividend.Classical.chat04_continuous_causal_convolution_integrable
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hzero : ∀ y : ℝ, y < 0 → g y = 0) (x : ℝ) :
    IntegrableOn (fun y : ℝ => f y * g (x - y)) (Ioi (0 : ℝ)) := by sorry
