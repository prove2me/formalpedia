-- Prove2me | Theorems.Thm_ActuarialAnnuities_guaranteed_due_arrears_correction
-- name    : ActuarialAnnuities.guaranteed_due_arrears_correction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:13:26.726286+00:00
-- url     : https://prove2.me/theorems/8d6f8889-03d0-47f1-ab68-747bb75aaf2a
-- title:
--   Guaranteed due arrears correction
-- statement:
--   Due/arrears correction must include the guaranteed estate-entitlement boundary. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{due},g}-V_{\text{arrears},g}=1-v^hS(h)+v^g[S(g)-1]
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Present value in GBP per unit nominal pension, with individual instalments in GBP, payment time in anniversaries and survival as dimensionless probability.
-- source:
--   Original derived finite annuity result. Contextual source page 148, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Due/arrears correction must include the guaranteed estate-entitlement boundary.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bSurvivalPV
import Definitions.Def_actuarial_bLevel

namespace ActuarialAnnuities

theorem guaranteed_due_arrears_correction (h g : ℕ) (v : ℝ) (p : ℕ → ℝ) (hg : g ≤ h) (hp : bTotal h p = 1) : bSurvivalPV h 0 h g 0 v (bLevel 1) p - bSurvivalPV h 0 h g 1 v (bLevel 1) p = 1-v^h*bSurvival h p h+v^g*(bSurvival h p g-1) := by sorry

end ActuarialAnnuities
