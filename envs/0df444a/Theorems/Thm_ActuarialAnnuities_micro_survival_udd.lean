-- Prove2me | Theorems.Thm_ActuarialAnnuities_micro_survival_udd
-- name    : ActuarialAnnuities.micro_survival_udd
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:11:30.052726+00:00
-- url     : https://prove2.me/theorems/6ebc5f93-7795-425b-8414-0174af891aff
-- title:
--   Micro survival udd
-- statement:
--   Derived subperiod survival equals UDD interpolation of neighbouring annual states. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   S^{(m)}(jm+r)=(1-r/m)S(j)+(r/m)S(j+1)
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Probability, dimensionless, indexed in whole micro-instalments.
-- source:
--   Original derived finite annuity result. Contextual source page 152, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Derived subperiod survival equals UDD interpolation of neighbouring annual states.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bUDD
import Definitions.Def_actuarial_bUDDMicroSurvival

namespace ActuarialAnnuities

theorem micro_survival_udd (h m q : ℕ) (p : ℕ → ℝ) (hm : 0 < m) (hq : q < h*m) : bUDDMicroSurvival h m p q = bUDD (bSurvival h p (q/m)) (bSurvival h p (q/m+1)) ((((q % m : ℕ) : ℝ)) / (m : ℝ)) := by sorry

end ActuarialAnnuities
