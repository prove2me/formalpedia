-- Prove2me | Theorems.Thm_ActuarialAnnuities_required_guarantee
-- name    : ActuarialAnnuities.required_guarantee
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:07:42.176127+00:00
-- url     : https://prove2.me/theorems/962d5736-6174-4a52-a36f-28c57e433d37
-- title:
--   Required guarantee
-- statement:
--   A guaranteed instalment requires survival to commencement, not its payment date. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   r_j=a\quad(j<a+g)
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Whole anniversary/payment index, dimensionless integer.
-- source:
--   Original derived finite annuity result. Contextual source page 143, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. A guaranteed instalment requires survival to commencement, not its payment date.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bRequiredAge

namespace ActuarialAnnuities

theorem required_guarantee (a g delta j : ℕ) (hj : j < a+g) : bRequiredAge a g delta j = a := by sorry

end ActuarialAnnuities
