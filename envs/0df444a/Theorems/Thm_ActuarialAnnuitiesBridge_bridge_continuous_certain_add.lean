-- Prove2me | Theorems.Thm_ActuarialAnnuitiesBridge_bridge_continuous_certain_add
-- name    : ActuarialAnnuitiesBridge.bridge_continuous_certain_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:37:22.945908+00:00
-- url     : https://prove2.me/theorems/df8aa361-64d2-4730-b19a-d7a8781d13f0
-- title:
--   Continuous annuity-certain integrals split exactly at a real-valued duration boundary.
-- statement:
--   Continuous annuity-certain integrals split exactly at a real-valued duration boundary. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   \int_a^{a+n_1+n_2}f(t)\,dt=\int_a^{a+n_1}f(t)\,dt+\int_{a+n_1}^{a+n_1+n_2}f(t)\,dt
--   $$
--
--   Units: time in years, GBP per year for continuous rates, and dimensionless survival/discount where applicable No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 152. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Continuous annuity-certain integrals split exactly at a real-valued duration boundary.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcCertainPV

namespace ActuarialAnnuitiesBridge

open MeasureTheory

theorem bridge_continuous_certain_add (a termA termB rho : ℝ) (b : ℝ → ℝ) (hA : 0 ≤ termA) (hB : 0 ≤ termB) (hint : IntervalIntegrable (fun t => b t * Real.exp (-rho*t)) MeasureTheory.volume a (a+termA+termB)) : ActuarialAnnuitiesContinuous.bcCertainPV a (termA+termB) rho b = ActuarialAnnuitiesContinuous.bcCertainPV a termA rho b + ActuarialAnnuitiesContinuous.bcCertainPV (a+termA) termB rho b := by sorry

end ActuarialAnnuitiesBridge
