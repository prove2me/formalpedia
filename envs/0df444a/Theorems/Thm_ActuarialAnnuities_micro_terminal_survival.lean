-- Prove2me | Theorems.Thm_ActuarialAnnuities_micro_terminal_survival
-- name    : ActuarialAnnuities.micro_terminal_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:11:43.36306+00:00
-- url     : https://prove2.me/theorems/b859f4b3-3ac8-4e9d-bd9c-1ab9b48bba51
-- title:
--   Micro terminal survival
-- statement:
--   Survival after the last right-censored subperiod vanishes in the finite construction. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   q>hm\Rightarrow S^{(m)}(q)=0
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Probability, dimensionless, indexed in whole micro-instalments.
-- source:
--   Original derived finite annuity result. Contextual source page 152, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Survival after the last right-censored subperiod vanishes in the finite construction.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bUDDMicroSurvival

namespace ActuarialAnnuities

theorem micro_terminal_survival (h m q : ℕ) (p : ℕ → ℝ) (hm : 0 < m) (hq : h*m < q) : bUDDMicroSurvival h m p q = 0 := by sorry

end ActuarialAnnuities
