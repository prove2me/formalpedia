-- Prove2me | Theorems.Thm_ActuarialAnnuitiesContinuous_bc_full_guarantee_certain
-- name    : ActuarialAnnuitiesContinuous.bc_full_guarantee_certain
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T20:16:39.448898+00:00
-- url     : https://prove2.me/theorems/37a482ed-953d-4165-84cc-574accf435df
-- title:
--   An activated entire-term guarantee equals conditional annuity-certain integral
-- statement:
--   An activated entire-term guarantee equals conditional annuity-certain integral. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   g\ge n\Longrightarrow V=S(a)V_{\text{certain}}
--   $$
--
--   Units: GBP for present values, years for time, and nonnegative dimensionless survival probabilities, as relevant No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 149. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. An activated entire-term guarantee equals conditional annuity-certain integral

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcSurvival
import Definitions.Def_actuarial_bcProjectedPV
import Definitions.Def_actuarial_bcCertainPV

namespace ActuarialAnnuitiesContinuous

open MeasureTheory

theorem bc_full_guarantee_certain (N : ℕ) (p : ℕ → ℝ) (life : ℕ → ℝ) (a term g rho : ℝ) (b : ℝ → ℝ) (hn : 0 ≤ term) (hg : term ≤ g) (hint : IntervalIntegrable (fun t => b t * Real.exp (-rho*t)) volume a (a+term)) : bcProjectedPV N p life a term g rho b = bcSurvival N p life a * bcCertainPV a term rho b := by sorry

end ActuarialAnnuitiesContinuous
