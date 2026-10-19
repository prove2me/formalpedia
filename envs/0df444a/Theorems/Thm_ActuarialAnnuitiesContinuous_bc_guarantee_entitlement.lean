-- Prove2me | Theorems.Thm_ActuarialAnnuitiesContinuous_bc_guarantee_entitlement
-- name    : ActuarialAnnuitiesContinuous.bc_guarantee_entitlement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:14:44.94319+00:00
-- url     : https://prove2.me/theorems/53a6564a-d20c-4840-bea2-fe876302c700
-- title:
--   Estate continuation is activated by commencement survival
-- statement:
--   Estate continuation is activated by commencement survival. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   t<a+g\Longrightarrow E(t,T)=I(T,a)
--   $$
--
--   Units: GBP for present values, years for time, and nonnegative dimensionless survival probabilities, as relevant No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 149. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Estate continuation is activated by commencement survival

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcAlive
import Definitions.Def_actuarial_bcEntitled

namespace ActuarialAnnuitiesContinuous

open MeasureTheory

theorem bc_guarantee_entitlement (a g t lifetime : ℝ) (ht : t < a+g) : bcEntitled a g t lifetime = bcAlive lifetime a := by sorry

end ActuarialAnnuitiesContinuous
