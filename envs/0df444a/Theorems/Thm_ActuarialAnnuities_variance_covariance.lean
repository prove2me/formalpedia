-- Prove2me | Theorems.Thm_ActuarialAnnuities_variance_covariance
-- name    : ActuarialAnnuities.variance_covariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:08:41.941927+00:00
-- url     : https://prove2.me/theorems/2082ef50-a361-4067-8654-497a2dcf1d22
-- title:
--   Variance covariance
-- statement:
--   Variance equals the sum of nested-life-event covariance terms, without independence. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   \operatorname{Var}(Z)=\sum_{i,j}c_ic_j[S(\max(r_i,r_j))-S(r_i)S(r_j)]
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Squared present value in GBP²; first moments and benefit amounts are GBP.
-- source:
--   Original derived finite annuity result. Contextual source page 143, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Variance equals the sum of nested-life-event covariance terms, without independence.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bVariance
import Definitions.Def_actuarial_bCovariancePV

namespace ActuarialAnnuities

theorem variance_covariance (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : bVariance h a n g delta v b p = bCovariancePV h a n g delta v b p := by sorry

end ActuarialAnnuities
