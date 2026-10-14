-- Prove2me | Theorems.Thm_ActuarialAnnuities_fractional_random_expectation
-- name    : ActuarialAnnuities.fractional_random_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:12:02.480001+00:00
-- url     : https://prove2.me/theorems/20e6b664-75b8-4368-b568-6f42e2dd72dd
-- title:
--   Fractional random expectation
-- statement:
--   Actual micro-state cashflow expectation equals an independently projected fractional UDD sum. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[Z^{(m)}]=\sum_qc_qw^{q+\delta}S^{(m)}(r_q)
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Present value in GBP per unit nominal pension, with individual instalments in GBP, payment time in anniversaries and survival as dimensionless probability.
-- source:
--   Original derived finite annuity result. Contextual source page 152, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Actual micro-state cashflow expectation equals an independently projected fractional UDD sum.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bFractionalExpectedPV
import Definitions.Def_actuarial_bFractionalSurvivalPV

namespace ActuarialAnnuities

theorem fractional_random_expectation (h a n g delta m : ℕ) (w : ℝ) (b p : ℕ → ℝ) : bFractionalExpectedPV h a n g delta m w b p = bFractionalSurvivalPV h a n g delta m w b p := by sorry

end ActuarialAnnuities
