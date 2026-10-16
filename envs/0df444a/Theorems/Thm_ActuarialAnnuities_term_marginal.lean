-- Prove2me | Theorems.Thm_ActuarialAnnuities_term_marginal
-- name    : ActuarialAnnuities.term_marginal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:09:58.417728+00:00
-- url     : https://prove2.me/theorems/b71e892d-707b-47b9-980f-b7a8a1dbe1ff
-- title:
--   Term marginal
-- statement:
--   Adding a payment year changes EPV by exactly its individual cashflow entitlement. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   V_{n+1}-V_n=b_{a+n}v^{a+n+\delta}\Pr(\text{payment at }a+n+\delta)
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Present value in GBP per unit nominal pension, with individual instalments in GBP, payment time in anniversaries and survival as dimensionless probability.
-- source:
--   Original derived finite annuity result. Contextual source page 157, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Adding a payment year changes EPV by exactly its individual cashflow entitlement.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bSurvivalPV

namespace ActuarialAnnuities

theorem term_marginal (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : bSurvivalPV h a (n+1) g delta v b p - bSurvivalPV h a n g delta v b p = if a+n < h then b (a+n)*v^(a+n+delta)*(if n < g then bSurvival h p a else bSurvival h p (a+n+delta)) else 0 := by sorry

end ActuarialAnnuities
