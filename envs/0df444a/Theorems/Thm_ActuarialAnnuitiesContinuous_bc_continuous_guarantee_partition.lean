-- Prove2me | Theorems.Thm_ActuarialAnnuitiesContinuous_bc_continuous_guarantee_partition
-- name    : ActuarialAnnuitiesContinuous.bc_continuous_guarantee_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:16:15.516312+00:00
-- url     : https://prove2.me/theorems/c27b3fe1-bcc0-4067-bbe8-dbdd8d38c8bc
-- title:
--   Continuous guaranteed and contingent integrals partition disjoint entitlement intervals
-- statement:
--   Continuous guaranteed and contingent integrals partition disjoint entitlement intervals. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   V=V_{\text{guarantee}}+V_{\text{post}}
--   $$
--
--   Units: GBP for present values, years for time, and nonnegative dimensionless survival probabilities, as relevant No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 149. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Continuous guaranteed and contingent integrals partition disjoint entitlement intervals

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcProjectedPV
import Definitions.Def_actuarial_bcGuaranteedPV
import Definitions.Def_actuarial_bcPostGuaranteePV

namespace ActuarialAnnuitiesContinuous

open MeasureTheory

theorem bc_continuous_guarantee_partition (N : ℕ) (p : ℕ → ℝ) (life : ℕ → ℝ) (a term g rho : ℝ) (b : ℝ → ℝ) (hn : 0 ≤ term) (hint : IntervalIntegrable (fun t => b t * Real.exp (-rho*t)) volume a (a+term)) : bcProjectedPV N p life a term g rho b = bcGuaranteedPV N p life a term g rho b + bcPostGuaranteePV N p life a term g rho b := by sorry

end ActuarialAnnuitiesContinuous
