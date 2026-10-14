-- Prove2me | Theorems.Thm_ActuarialAnnuities_guarantee_marginal_nonnegative
-- name    : ActuarialAnnuities.guarantee_marginal_nonnegative
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T20:09:42.505994+00:00
-- url     : https://prove2.me/theorems/52922f8c-7c25-4339-88a8-5b25e8f89f1c
-- title:
--   Guarantee marginal nonnegative
-- statement:
--   Extending an estate-continuation guarantee cannot reduce value for nonnegative benefits. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   V_{g+1}\ge V_g
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Present value in GBP per unit nominal pension, with individual instalments in GBP, payment time in anniversaries and survival as dimensionless probability.
-- source:
--   Original derived finite annuity result. Contextual source page 159, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Extending an estate-continuation guarantee cannot reduce value for nonnegative benefits.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvivalPV

namespace ActuarialAnnuities

theorem guarantee_marginal_nonnegative (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hv : 0 ≤ v) (hb : ∀ j, 0 ≤ b j) (hp : ∀ k, 0 ≤ p k) : bSurvivalPV h a n g delta v b p ≤ bSurvivalPV h a n (g+1) delta v b p := by sorry

end ActuarialAnnuities
