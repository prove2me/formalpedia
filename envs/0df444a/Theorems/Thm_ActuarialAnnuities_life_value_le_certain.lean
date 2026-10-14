-- Prove2me | Theorems.Thm_ActuarialAnnuities_life_value_le_certain
-- name    : ActuarialAnnuities.life_value_le_certain
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T20:10:29.042997+00:00
-- url     : https://prove2.me/theorems/600c08a8-31a1-4600-80a7-3f23c7c8d9f4
-- title:
--   Life value le certain
-- statement:
--   Survival entitlement bounds the life-annuity PV above by the matching annuity-certain value. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   0\le V_{\text{life}}\le V_{\text{certain}}
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Present value in GBP per unit nominal pension, with individual instalments in GBP, payment time in anniversaries and survival as dimensionless probability.
-- source:
--   Original derived finite annuity result. Contextual source page 142, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Survival entitlement bounds the life-annuity PV above by the matching annuity-certain value.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bExpectedPV
import Definitions.Def_actuarial_bCertainPV

namespace ActuarialAnnuities

theorem life_value_le_certain (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hv : 0 ≤ v) (hb : ∀ j, 0 ≤ b j) (hp : ∀ k, 0 ≤ p k) (hs : bTotal h p = 1) : bExpectedPV h a n g delta v b p ≤ bCertainPV h a n delta v b := by sorry

end ActuarialAnnuities
