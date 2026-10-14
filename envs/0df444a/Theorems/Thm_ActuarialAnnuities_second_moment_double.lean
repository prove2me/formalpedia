-- Prove2me | Theorems.Thm_ActuarialAnnuities_second_moment_double
-- name    : ActuarialAnnuities.second_moment_double
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:08:23.201182+00:00
-- url     : https://prove2.me/theorems/723eec25-2494-4209-a2f2-dca18a6ca0ff
-- title:
--   Second moment double
-- statement:
--   Reconcile actual pathwise squared PV with pairwise intersection survival probabilities. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[Z^2]=\sum_{i,j}c_ic_jS(\max(r_i,r_j))
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Squared present value in GBP²; first moments and benefit amounts are GBP.
-- source:
--   Original derived finite annuity result. Contextual source page 143, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Reconcile actual pathwise squared PV with pairwise intersection survival probabilities.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSecondMoment
import Definitions.Def_actuarial_bProjectedSecondMoment

namespace ActuarialAnnuities

theorem second_moment_double (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : bSecondMoment h a n g delta v b p = bProjectedSecondMoment h a n g delta v b p := by sorry

end ActuarialAnnuities
