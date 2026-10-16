-- Prove2me | Theorems.Thm_ActuarialAnnuities_guarantee_marginal
-- name    : ActuarialAnnuities.guarantee_marginal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:09:26.893973+00:00
-- url     : https://prove2.me/theorems/d7a53a71-bfd4-4574-9ada-a89f20c4bd3f
-- title:
--   Guarantee marginal
-- statement:
--   One additional guaranteed instalment has exactly its probability-of-death uplift. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   V_{g+1}-V_g=b_{a+g}v^{a+g+\delta}[S(a)-S(a+g+\delta)]
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Present value in GBP per unit nominal pension, with individual instalments in GBP, payment time in anniversaries and survival as dimensionless probability.
-- source:
--   Original derived finite annuity result. Contextual source page 159, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. One additional guaranteed instalment has exactly its probability-of-death uplift.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bSurvivalPV

namespace ActuarialAnnuities

theorem guarantee_marginal (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : bSurvivalPV h a n (g+1) delta v b p - bSurvivalPV h a n g delta v b p = if a+g < h ∧ a+g < a+n then b (a+g)*v^(a+g+delta)*(bSurvival h p a-bSurvival h p (a+g+delta)) else 0 := by sorry

end ActuarialAnnuities
