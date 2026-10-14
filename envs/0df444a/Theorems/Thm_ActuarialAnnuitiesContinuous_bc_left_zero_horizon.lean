-- Prove2me | Theorems.Thm_ActuarialAnnuitiesContinuous_bc_left_zero_horizon
-- name    : ActuarialAnnuitiesContinuous.bc_left_zero_horizon
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T20:16:59.546996+00:00
-- url     : https://prove2.me/theorems/356edc17-0650-4266-8b31-09525153ad2b
-- title:
--   Zero time horizon makes all instalment sums empty
-- statement:
--   Zero time horizon makes all instalment sums empty. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   R_m(f,H=0)=0
--   $$
--
--   Units: GBP for present values, years for time, and nonnegative dimensionless survival probabilities, as relevant No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 166. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Zero time horizon makes all instalment sums empty

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcLeftRiemann

namespace ActuarialAnnuitiesContinuous

open MeasureTheory

theorem bc_left_zero_horizon (m : ℕ) (f : ℝ → ℝ) : bcLeftRiemann 0 m f = 0 := by sorry

end ActuarialAnnuitiesContinuous
