-- Prove2me | Theorems.Thm_ActuarialAnnuities_udd_due_frequency_limit
-- name    : ActuarialAnnuities.udd_due_frequency_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T06:39:36.189809+00:00
-- url     : https://prove2.me/theorems/f27c0583-e1e9-4c29-bdbf-22ac47090fa6
-- title:
--   True high-frequency convergence of UDD annuity-due valuations to the integral of the continuous piecewise-linear survivor curve.
-- statement:
--   True high-frequency convergence of UDD annuity-due valuations to the integral of the continuous piecewise-linear survivor curve.
--
--   Mathematical relation:
--
--   $$
--   \lim_{m\to\infty}a_{\text{due}}^{(m)}=C
--   $$
--
--   Units: GBP per unit yearly nominal benefit; m is positive instalments per year, survival is dimensionless. All displayed results are open Lean theorem statements, not accepted proofs.
-- source:
--   Original derived actuarial result, contextual source page 166. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5, Cambridge University Press. https://doi.org/10.1017/9781108784184 This exact finite UDD payment-event identity, including terminal censoring and instalment scale, is original to this formalisation; it is not a verbatim numbered theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bFractionalSurvivalPV
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bUDDTrapezoidPV

namespace ActuarialAnnuities

theorem udd_due_frequency_limit (h : ℕ) (p : ℕ → ℝ) :
    Filter.Tendsto (fun m : ℕ =>
      bFractionalSurvivalPV h 0 h 0 0 (m+1) 1 (fun _ => 1) p)
      Filter.atTop (nhds (bUDDTrapezoidPV h p)) := by sorry

end ActuarialAnnuities
