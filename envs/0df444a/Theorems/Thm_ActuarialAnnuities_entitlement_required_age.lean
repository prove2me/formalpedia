-- Prove2me | Theorems.Thm_ActuarialAnnuities_entitlement_required_age
-- name    : ActuarialAnnuities.entitlement_required_age
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:08:08.59656+00:00
-- url     : https://prove2.me/theorems/6eabed94-7504-4505-a5a1-2bfaf9946e83
-- title:
--   Entitlement required age
-- statement:
--   Unify actual payment events into a single required-survival-age kernel. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   E_{a,g,\delta}(j,k)=\mathbf1_{\{k\ge r_j\}}
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Whole anniversary/payment index, dimensionless integer.
-- source:
--   Original derived finite annuity result. Contextual source page 143, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Unify actual payment events into a single required-survival-age kernel.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bAlive
import Definitions.Def_actuarial_bEntitlement
import Definitions.Def_actuarial_bRequiredAge

namespace ActuarialAnnuities

theorem entitlement_required_age (a g delta j k : ℕ) : bEntitlement a g delta j k = bAlive k (bRequiredAge a g delta j) := by sorry

end ActuarialAnnuities
