-- Prove2me | Theorems.Thm_ActuarialAnnuities_fractional_one_instalment
-- name    : ActuarialAnnuities.fractional_one_instalment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:12:15.556306+00:00
-- url     : https://prove2.me/theorems/34385865-7248-4af0-8c56-70f532da3d05
-- title:
--   Fractional one instalment
-- statement:
--   One payment per year recovers the original annual survival-contingent contract exactly. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   V^{(1)}=V^{\text{annual}}
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Present value in GBP per unit nominal pension, with individual instalments in GBP, payment time in anniversaries and survival as dimensionless probability.
-- source:
--   Original derived finite annuity result. Contextual source page 152, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. One payment per year recovers the original annual survival-contingent contract exactly.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bExpectedPV
import Definitions.Def_actuarial_bFractionalExpectedPV

namespace ActuarialAnnuities

theorem fractional_one_instalment (h a n g delta : ℕ) (w : ℝ) (b p : ℕ → ℝ) : bFractionalExpectedPV h a n g delta 1 w b p = bExpectedPV h a n g delta w b p := by sorry

end ActuarialAnnuities
