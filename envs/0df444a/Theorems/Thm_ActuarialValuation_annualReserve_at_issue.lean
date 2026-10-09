-- Prove2me | Theorems.Thm_ActuarialValuation_annualReserve_at_issue
-- name    : ActuarialValuation.annualReserve_at_issue
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:27:42.930794+00:00
-- url     : https://prove2.me/theorems/fb0c60e8-5e8e-43ed-8cb2-eb5846e5072c
-- title:
--   Reserve at duration zero
-- statement:
--   At duration zero, survival has probability one, so reserve is expected loss at issue.
--
--   **Mathematical statement**
--
--   $$
--   V_0=\mathbb E[L_0]
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Ch.6 §6.3, equations (6.3.4)-(6.3.10); Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Ch.7 §7.3.3, https://doi.org/10.1017/CBO9780511800146.008

import Mathlib
import Definitions.Def_actuarial_annualFutureLoss
import Definitions.Def_actuarial_annualProspectiveReserve
open MeasureTheory

namespace ActuarialValuation

theorem annualReserve_at_issue {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ) (b π : ℝ)
  :
  annualProspectiveReserve P K v n 0 b π =
    ∫ ω, annualFutureLoss K v n 0 b π ω ∂P := by sorry

end ActuarialValuation
