-- Prove2me | Theorems.Thm_ActuarialValuation_annualFutureLoss_integrable
-- name    : ActuarialValuation.annualFutureLoss_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:20:24.326696+00:00
-- url     : https://prove2.me/theorems/479f39ac-60d8-43ed-9cb1-bf2b3bfc59e6
-- title:
--   Finite future net loss integrability
-- statement:
--   The finite future payment range is measurable and bounded for fixed real cashflow and discount parameters.
--
--   **Mathematical statement**
--
--   $$
--   L_t\in L^1(P)
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Ch.6 §6.3, equations (6.3.4)-(6.3.10); Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Ch.7 §7.3.3, https://doi.org/10.1017/CBO9780511800146.008

import Mathlib
import Definitions.Def_actuarial_annualFutureLoss
open MeasureTheory

namespace ActuarialValuation

theorem annualFutureLoss_integrable {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ) (hK : Measurable K)
  (v : ℝ) (n t : ℕ) (b π : ℝ)
  :
  Integrable (annualFutureLoss K v n t b π) P := by sorry

end ActuarialValuation
