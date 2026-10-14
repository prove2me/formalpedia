-- Prove2me | Theorems.Thm_ActuarialAnnuitiesBridge_root_annual_fractional_continuous_reconciliation
-- name    : ActuarialAnnuitiesBridge.root_annual_fractional_continuous_reconciliation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T06:48:54.470383+00:00
-- url     : https://prove2.me/theorems/04f67506-69b0-4ae5-85c1-73145161e42f
-- title:
--   Unified actual single-life annuity valuation across annual, fractional and continuous payment modes
-- statement:
--   Under one properly normalised censored lifetime-state law, the actual annual advance and arrears, UDD micro-instalment, and real-time continuous payment present values independently agree with their survival-weighted valuations, while real-time and annual survival agree at commencement. The continuous guarantees partition at their contractual expiry. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[Z_{\text{annual}}]=V_{\text{annual}},\quad\mathbb E[Z^{(m)}]=V^{(m)},\quad\mathbb E[Z_{\text{continuous}}]=V_{\text{continuous}}
--   $$
--
--   Units: GBP per actual instalment and GBP per year for continuous rates; time in years, state probabilities dimensionless No open mathematical statement in this Draft is represented as a proved theorem.
--
--   This stronger form uses UDD microstate death times for the real-time integral and additionally proves the finite UDD annuity-due correction and equality of the continuous microstate cashflow with the corresponding arrears valuation. It uses the same microstate law at each fixed frequency.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 143. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Under one properly normalised censored lifetime-state law, the actual annual advance and arrears, UDD micro-instalment, and real-time continuous payment present values independently agree with their survival-weighted valuations, while real-time and annual survival agree at commencement. The continuous guarantees partition at their contractual expiry.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bExpectedPV
import Definitions.Def_actuarial_bSurvivalPV
import Definitions.Def_actuarial_bFractionalExpectedPV
import Definitions.Def_actuarial_bFractionalSurvivalPV
import Definitions.Def_actuarial_bcSurvival
import Definitions.Def_actuarial_bcExpectedPV
import Definitions.Def_actuarial_bcProjectedPV
import Definitions.Def_actuarial_bcGuaranteedPV
import Definitions.Def_actuarial_bcPostGuaranteePV
import Definitions.Def_actuarial_bUDDTrapezoidPV
import Definitions.Def_actuarial_bUDDMicroMass
import Definitions.Def_actuarial_bUDDMicroSurvival

namespace ActuarialAnnuitiesBridge

open MeasureTheory

theorem root_annual_fractional_continuous_reconciliation
    (h a n g m : ℕ) (v w rho : ℝ)
    (b p : ℕ → ℝ) (rate : ℝ → ℝ)
    (hm : 0 < m)
    (hp : ActuarialAnnuities.bTotal h p = 1)
    (hprob : ∀ k, 0 ≤ p k)
    (hv : 0 < v) (hw : 0 < w)
    (hi : IntervalIntegrable (fun t => rate t * Real.exp (-rho*t))
        volume (a : ℝ) ((a : ℝ)+(n : ℝ))) :
    (ActuarialAnnuities.bExpectedPV h a n g 0 v b p
        = ActuarialAnnuities.bSurvivalPV h a n g 0 v b p)
    ∧ (ActuarialAnnuities.bExpectedPV h a n g 1 v b p
        = ActuarialAnnuities.bSurvivalPV h a n g 1 v b p)
    ∧ (ActuarialAnnuities.bFractionalExpectedPV h a n g 0 m w b p
        = ActuarialAnnuities.bFractionalSurvivalPV h a n g 0 m w b p)
    ∧ (ActuarialAnnuitiesContinuous.bcExpectedPV (h*m) (ActuarialAnnuities.bUDDMicroMass h m p) (fun k => (k : ℝ)/(m : ℝ))
         (a : ℝ) (n : ℝ) (g : ℝ) rho rate
       = ActuarialAnnuitiesContinuous.bcProjectedPV (h*m) (ActuarialAnnuities.bUDDMicroMass h m p) (fun k => (k : ℝ)/(m : ℝ))
         (a : ℝ) (n : ℝ) (g : ℝ) rho rate)
    ∧ (ActuarialAnnuitiesContinuous.bcProjectedPV (h*m) (ActuarialAnnuities.bUDDMicroMass h m p) (fun k => (k : ℝ)/(m : ℝ))
         (a : ℝ) (n : ℝ) (g : ℝ) rho rate
       = ActuarialAnnuitiesContinuous.bcGuaranteedPV (h*m) (ActuarialAnnuities.bUDDMicroMass h m p) (fun k => (k : ℝ)/(m : ℝ))
         (a : ℝ) (n : ℝ) (g : ℝ) rho rate
         + ActuarialAnnuitiesContinuous.bcPostGuaranteePV (h*m) (ActuarialAnnuities.bUDDMicroMass h m p) (fun k => (k : ℝ)/(m : ℝ))
         (a : ℝ) (n : ℝ) (g : ℝ) rho rate)
    ∧ (ActuarialAnnuitiesContinuous.bcSurvival (h*m)
         (ActuarialAnnuities.bUDDMicroMass h m p)
         (fun k => (k : ℝ)/(m : ℝ)) ((a*m : ℕ) : ℝ)/(m : ℝ)
        = ActuarialAnnuities.bUDDMicroSurvival h m p (a*m))
    ∧ (ActuarialAnnuitiesContinuous.bcSurvival (h*m)
         (ActuarialAnnuities.bUDDMicroMass h m p)
         (fun k => (k : ℝ)/(m : ℝ)) (a : ℝ)
        = ActuarialAnnuities.bSurvival h p a)
    ∧ (ActuarialAnnuities.bFractionalSurvivalPV h 0 h 0 0 m 1 (fun _ => 1) p
         = ActuarialAnnuities.bUDDTrapezoidPV h p
          + (ActuarialAnnuities.bSurvival h p 0
              - ActuarialAnnuities.bSurvival h p h)/(2*(m : ℝ)))
    ∧ (ActuarialAnnuitiesContinuous.bcExpectedPV (h*m)
      (ActuarialAnnuities.bUDDMicroMass h m p)
      (fun k => (k : ℝ)/(m : ℝ))
      0 (h : ℝ) 0 0 (fun _ => 1)
        = ActuarialAnnuities.bFractionalSurvivalPV h 0 h 0 1 m 1 (fun _ => 1) p) := by sorry

end ActuarialAnnuitiesBridge
