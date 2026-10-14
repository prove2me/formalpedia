-- Prove2me | Theorems.Thm_ActuarialAnnuities_fractional_empty_term
-- name    : ActuarialAnnuities.fractional_empty_term
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:13:04.190091+00:00
-- url     : https://prove2.me/theorems/4066e1bc-2f35-4a8e-a014-ac721e97ae2a
-- title:
--   Fractional empty term
-- statement:
--   Fractional zero-duration payment streams have zero expected PV. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   n=0\Rightarrow V^{(m)}=0
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Present value in GBP per unit nominal pension, with individual instalments in GBP, payment time in anniversaries and survival as dimensionless probability.
-- source:
--   Original derived finite annuity result. Contextual source page 152, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Fractional zero-duration payment streams have zero expected PV.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bFractionalExpectedPV

namespace ActuarialAnnuities

theorem fractional_empty_term (h a g delta m : ℕ) (w : ℝ) (b p : ℕ → ℝ) : bFractionalExpectedPV h a 0 g delta m w b p = 0 := by sorry

end ActuarialAnnuities
