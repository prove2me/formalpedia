-- Prove2me | Theorems.Thm_ActuarialAnnuitiesBridge_udd_micro_continuous_equals_arrears
-- name    : ActuarialAnnuitiesBridge.udd_micro_continuous_equals_arrears
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T06:39:58.560676+00:00
-- url     : https://prove2.me/theorems/7a05f36f-83c2-4c7b-b7d4-4832ef9fd816
-- title:
--   Continuous payments under one discrete subperiod-atom lifetime law equal the right-end m-thly arrears sum at zero interest.
-- statement:
--   Continuous payments under one discrete subperiod-atom lifetime law equal the right-end m-thly arrears sum at zero interest.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{continuous, micro}}=a_{\text{arrears}}^{(m)}
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
import Definitions.Def_actuarial_bUDDMicroMass
import Definitions.Def_actuarial_bcExpectedPV
import Definitions.Def_actuarial_bFractionalSurvivalPV

namespace ActuarialAnnuitiesBridge

open MeasureTheory

theorem udd_micro_continuous_equals_arrears (h m : ℕ) (p : ℕ → ℝ)
   (hm : 0 < m) :
    ActuarialAnnuitiesContinuous.bcExpectedPV (h*m)
      (ActuarialAnnuities.bUDDMicroMass h m p)
      (fun k => (k : ℝ)/(m : ℝ))
      0 (h : ℝ) 0 0 (fun _ => 1)
    = ActuarialAnnuities.bFractionalSurvivalPV h 0 h 0 1 m 1 (fun _ => 1) p := by sorry

end ActuarialAnnuitiesBridge
