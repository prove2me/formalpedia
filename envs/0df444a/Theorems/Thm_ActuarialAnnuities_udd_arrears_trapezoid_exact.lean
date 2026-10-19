-- Prove2me | Theorems.Thm_ActuarialAnnuities_udd_arrears_trapezoid_exact
-- name    : ActuarialAnnuities.udd_arrears_trapezoid_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:38:24.725526+00:00
-- url     : https://prove2.me/theorems/b608f207-d48f-4af3-8461-c26b68296896
-- title:
--   Exact UDD m-thly annuity-arrears correction with payment conditional on survival at each final subperiod instant.
-- statement:
--   Exact UDD m-thly annuity-arrears correction with payment conditional on survival at each final subperiod instant.
--
--   Mathematical relation:
--
--   $$
--   a_{\text{arrears}}^{(m)}=C-\frac{S(0)-S(h)}{2m}
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

theorem udd_arrears_trapezoid_exact (h m : ℕ) (p : ℕ → ℝ) (hm : 0 < m) :
  bFractionalSurvivalPV h 0 h 0 1 m 1 (fun _ => 1) p =
    bUDDTrapezoidPV h p - (bSurvival h p 0-bSurvival h p h)/(2*(m : ℝ)) := by sorry

end ActuarialAnnuities
