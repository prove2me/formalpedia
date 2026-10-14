-- Prove2me | Theorems.Thm_ActuarialAnnuitiesBridge_bridge_guaranteed_certain_integral
-- name    : ActuarialAnnuitiesBridge.bridge_guaranteed_certain_integral
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T06:37:02.851276+00:00
-- url     : https://prove2.me/theorems/e6dd2b75-36de-4ebd-91b3-1a520b3e6de4
-- title:
--   An activated zero-interest continuous GBP 1 per year guarantee over g years equals commencement survival probability multiplied by the exact certain interval length.
-- statement:
--   An activated zero-interest continuous GBP 1 per year guarantee over g years equals commencement survival probability multiplied by the exact certain interval length. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   S(a)\int_a^{a+g}1\,dt=S(a)g
--   $$
--
--   Units: time in years, GBP per year for continuous rates, and dimensionless survival/discount where applicable No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 152. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. An activated zero-interest continuous GBP 1 per year guarantee over g years equals commencement survival probability multiplied by the exact certain interval length.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bcSurvival
import Definitions.Def_actuarial_bcCertainPV

namespace ActuarialAnnuitiesBridge

open MeasureTheory

theorem bridge_guaranteed_certain_integral (h a g : ℕ) (p : ℕ → ℝ) : ActuarialAnnuitiesContinuous.bcSurvival h p (fun k => (k : ℝ)) (a : ℝ) * ActuarialAnnuitiesContinuous.bcCertainPV (a : ℝ) (g : ℝ) 0 (fun _ => 1) = ActuarialAnnuities.bSurvival h p a * (g : ℝ) := by sorry

end ActuarialAnnuitiesBridge
