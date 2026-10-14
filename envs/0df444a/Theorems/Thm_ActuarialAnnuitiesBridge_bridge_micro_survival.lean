-- Prove2me | Theorems.Thm_ActuarialAnnuitiesBridge_bridge_micro_survival
-- name    : ActuarialAnnuitiesBridge.bridge_micro_survival
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T06:36:17.950144+00:00
-- url     : https://prove2.me/theorems/19ff51f2-1457-4322-aad6-ba1478e76515
-- title:
--   Real-time survival constructed from UDD micro-state masses equals the indexed quarterly or m-thly survival law at every micro-instalment boundary.
-- statement:
--   Real-time survival constructed from UDD micro-state masses equals the indexed quarterly or m-thly survival law at every micro-instalment boundary. The survival entitlement and timing are fixed by the actual underlying contractual payment event.
--
--   Mathematical relation:
--
--   $$
--   S_{\text{real}}(q/m)=S^{(m)}(q)
--   $$
--
--   Units: time in years, GBP per year for continuous rates, and dimensionless survival/discount where applicable No open mathematical statement in this Draft is represented as a proved theorem.
-- source:
--   Original derived finite/continuous single-life annuity result, contextual source page 152. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press, Chapter 5. https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The original mathematical construction is an extension of the chapter's payment timing and survival valuation framework; it is not claimed as a literal numbered theorem. Real-time survival constructed from UDD micro-state masses equals the indexed quarterly or m-thly survival law at every micro-instalment boundary.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bUDDMicroMass
import Definitions.Def_actuarial_bUDDMicroSurvival
import Definitions.Def_actuarial_bcSurvival

namespace ActuarialAnnuitiesBridge

open MeasureTheory

theorem bridge_micro_survival (h m q : ℕ) (p : ℕ → ℝ) (hm : 0 < m) : ActuarialAnnuitiesContinuous.bcSurvival (h*m) (ActuarialAnnuities.bUDDMicroMass h m p) (fun k => (k : ℝ)/(m : ℝ)) ((q : ℝ)/(m : ℝ)) = ActuarialAnnuities.bUDDMicroSurvival h m p q := by sorry

end ActuarialAnnuitiesBridge
