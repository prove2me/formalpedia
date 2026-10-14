-- Prove2me | Theorems.Thm_ActuarialAnnuities_fractional_quarterly_udd_example
-- name    : ActuarialAnnuities.fractional_quarterly_udd_example
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:13:15.149994+00:00
-- url     : https://prove2.me/theorems/96ad0863-ce8c-4901-8403-22cf30b7391d
-- title:
--   Fractional quarterly udd example
-- statement:
--   Exact quarterly UDD annuity-due worked case with £1 annual rate and zero interest. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   V^{(4)}_{\text{due}}=63/32
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Present value in GBP per unit nominal pension, with individual instalments in GBP, payment time in anniversaries and survival as dimensionless probability.
-- source:
--   Original derived finite annuity result. Contextual source page 152, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Exact quarterly UDD annuity-due worked case with £1 annual rate and zero interest.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bFractionalExpectedPV

namespace ActuarialAnnuities

theorem fractional_quarterly_udd_example : bFractionalExpectedPV 3 0 3 0 0 4 1 (fun _ => 1) (fun k => if k ≤ 3 then (1/4 : ℝ) else 0) = 63/32 := by sorry

end ActuarialAnnuities
