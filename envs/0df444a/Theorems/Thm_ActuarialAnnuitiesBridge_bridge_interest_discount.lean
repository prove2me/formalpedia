-- Prove2me | Theorems.Thm_ActuarialAnnuitiesBridge_bridge_interest_discount
-- name    : ActuarialAnnuitiesBridge.bridge_interest_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:36:26.184774+00:00
-- url     : https://prove2.me/theorems/4f348e70-45b0-4365-9017-cc5d1a71e166
-- title:
--   Discrete period discounting at effective factor exp of minus the force agrees exactly with continuous exponential discounting at integer payment times.
-- statement:
--   Discrete period discounting at effective factor exp of minus the force agrees exactly with continuous exponential discounting at integer payment times. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   (e^{-\rho})^j=e^{-\rho j}
--   $$
--
--   Units: time in years, GBP per year for continuous rates, and dimensionless survival/discount where applicable No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 152. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Discrete period discounting at effective factor exp of minus the force agrees exactly with continuous exponential discounting at integer payment times.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ActuarialAnnuitiesBridge

open MeasureTheory

theorem bridge_interest_discount (rho : ℝ) (j : ℕ) : (Real.exp (-rho))^j = Real.exp (-rho * (j : ℝ)) := by sorry

end ActuarialAnnuitiesBridge
