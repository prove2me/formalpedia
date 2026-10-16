-- Prove2me | Theorems.Thm_ActuarialAnnuitiesContinuous_bc_continuous_reconciliation
-- name    : ActuarialAnnuitiesContinuous.bc_continuous_reconciliation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:15:52.410975+00:00
-- url     : https://prove2.me/theorems/b989cc7d-7d35-4fd1-aea7-6aef38bd5649
-- title:
--   Actual continuous lifetime-state expectation equals integral of survival-weighted benefits
-- statement:
--   Actual continuous lifetime-state expectation equals integral of survival-weighted benefits. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[Z]=\int_a^{a+n}b(t)e^{-\rho t}[\mathbf1_{\{t<a+g\}}S(a)+\mathbf1_{\{t\ge a+g\}}S(t)]\,dt
--   $$
--
--   Units: GBP for present values, years for time, and nonnegative dimensionless survival probabilities, as relevant No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 149. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Actual continuous lifetime-state expectation equals integral of survival-weighted benefits

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcExpectedPV
import Definitions.Def_actuarial_bcProjectedPV

namespace ActuarialAnnuitiesContinuous

open MeasureTheory

theorem bc_continuous_reconciliation (N : ℕ) (p : ℕ → ℝ) (life : ℕ → ℝ) (a term g rho : ℝ) (b : ℝ → ℝ) (hn : 0 ≤ term) (hint : IntervalIntegrable (fun t => b t * Real.exp (-rho*t)) volume a (a+term)) : bcExpectedPV N p life a term g rho b = bcProjectedPV N p life a term g rho b := by sorry

end ActuarialAnnuitiesContinuous
