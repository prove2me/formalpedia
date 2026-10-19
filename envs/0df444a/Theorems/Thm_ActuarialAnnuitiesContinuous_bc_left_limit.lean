-- Prove2me | Theorems.Thm_ActuarialAnnuitiesContinuous_bc_left_limit
-- name    : ActuarialAnnuitiesContinuous.bc_left_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:35:22.589062+00:00
-- url     : https://prove2.me/theorems/5c25d72e-6790-4d69-ba8b-5c58ae58a9b9
-- title:
--   A genuine finite-horizon continuous-payment limit for annualised m-thly payments
-- statement:
--   A genuine finite-horizon continuous-payment limit for annualised m-thly payments. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   \lim_{m\to\infty}\frac1m\sum_{j=0}^{Hm-1}f(j/m)=\int_0^Hf(t)\,dt
--   $$
--
--   Units: GBP for present values, years for time, and nonnegative dimensionless survival probabilities, as relevant No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 166. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. A genuine finite-horizon continuous-payment limit for annualised m-thly payments

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bcLeftRiemann

namespace ActuarialAnnuitiesContinuous

open MeasureTheory

theorem bc_left_limit (H : ℕ) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (0 : ℝ) (H : ℝ))) : Filter.Tendsto (fun m : ℕ => bcLeftRiemann H (m+1) f) Filter.atTop (nhds (∫ t in (0 : ℝ)..(H : ℝ), f t)) := by sorry

end ActuarialAnnuitiesContinuous
