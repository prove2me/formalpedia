-- Prove2me | Theorems.Thm_ActuarialAnnuitiesContinuous_bc_alive_postdeath
-- name    : ActuarialAnnuitiesContinuous.bc_alive_postdeath
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T20:14:21.643263+00:00
-- url     : https://prove2.me/theorems/23ee6775-47c5-4946-8183-7f50601af359
-- title:
--   Survival indicator after death
-- statement:
--   Survival indicator after death. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   T<t\Longrightarrow I(T,t)=0
--   $$
--
--   Units: GBP for present values, years for time, and nonnegative dimensionless survival probabilities, as relevant No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 149. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Survival indicator after death

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcAlive

namespace ActuarialAnnuitiesContinuous

open MeasureTheory

theorem bc_alive_postdeath (lifetime t : ℝ) (ht : lifetime < t) : bcAlive lifetime t = 0 := by sorry

end ActuarialAnnuitiesContinuous
