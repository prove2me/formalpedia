-- Prove2me | Theorems.Thm_ActuarialAnnuities_required_postguarantee
-- name    : ActuarialAnnuities.required_postguarantee
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:07:55.042917+00:00
-- url     : https://prove2.me/theorems/791df91e-21e7-46eb-893f-b86e02cb3953
-- title:
--   Required postguarantee
-- statement:
--   A post-guarantee instalment requires actual payment-time survival. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   r_j=j+\delta\quad(j\ge a+g)
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Whole anniversary/payment index, dimensionless integer.
-- source:
--   Original derived finite annuity result. Contextual source page 143, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. A post-guarantee instalment requires actual payment-time survival.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bRequiredAge

namespace ActuarialAnnuities

theorem required_postguarantee (a g delta j : ℕ) (hj : a+g ≤ j) : bRequiredAge a g delta j = j+delta := by sorry

end ActuarialAnnuities
