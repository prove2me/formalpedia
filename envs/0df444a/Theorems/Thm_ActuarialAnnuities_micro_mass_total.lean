-- Prove2me | Theorems.Thm_ActuarialAnnuities_micro_mass_total
-- name    : ActuarialAnnuities.micro_mass_total
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:11:16.284042+00:00
-- url     : https://prove2.me/theorems/4e57257b-b62b-489c-bb2b-b7df523a13f3
-- title:
--   Micro mass total
-- statement:
--   Uniform subperiod splitting preserves total probability including terminal survivor mass. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   \sum_qp^{(m)}_q=\sum_kp_k
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Probability, dimensionless, indexed in whole micro-instalments.
-- source:
--   Original derived finite annuity result. Contextual source page 152, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Uniform subperiod splitting preserves total probability including terminal survivor mass.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bUDDMicroMass

namespace ActuarialAnnuities

theorem micro_mass_total (h m : ℕ) (p : ℕ → ℝ) (hm : 0 < m) : bTotal (h*m) (bUDDMicroMass h m p) = bTotal h p := by sorry

end ActuarialAnnuities
