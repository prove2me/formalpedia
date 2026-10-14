-- Prove2me | Theorems.Thm_ActuarialAnnuities_udd_due_trapezoid_error_bound
-- name    : ActuarialAnnuities.udd_due_trapezoid_error_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T06:39:04.294407+00:00
-- url     : https://prove2.me/theorems/886f3695-a447-4d35-8fde-73fccbf30b61
-- title:
--   Uniform positive correction bound under nonnegative total-one mortality masses.
-- statement:
--   Uniform positive correction bound under nonnegative total-one mortality masses.
--
--   Mathematical relation:
--
--   $$
--   0\le a_{\text{due}}^{(m)}-C\le \frac{1}{2m}
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
import Definitions.Def_actuarial_bTotal

namespace ActuarialAnnuities

theorem udd_due_trapezoid_error_bound (h m : ℕ) (p : ℕ → ℝ)
    (hm : 0 < m) (hp : ∀ k, 0 ≤ p k) (ht : bTotal h p = 1) :
    0 ≤ bFractionalSurvivalPV h 0 h 0 0 m 1 (fun _ => 1) p - bUDDTrapezoidPV h p
    ∧ bFractionalSurvivalPV h 0 h 0 0 m 1 (fun _ => 1) p - bUDDTrapezoidPV h p
         ≤ 1/(2*(m : ℝ)) := by sorry

end ActuarialAnnuities
