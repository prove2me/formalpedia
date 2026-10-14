-- Prove2me | Theorems.Thm_ActuarialAnnuities_assurance_at_zero_interest
-- name    : ActuarialAnnuities.assurance_at_zero_interest
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:09:14.702112+00:00
-- url     : https://prove2.me/theorems/fb18a6f6-d1d9-4e34-9bd9-13240b01eede
-- title:
--   Assurance at zero interest
-- statement:
--   Without discount, assurance equals the probability mass that dies within the finite horizon. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   A^{(h)}(v=1)=M_h-p_h
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Present value in GBP per unit nominal pension, with individual instalments in GBP, payment time in anniversaries and survival as dimensionless probability.
-- source:
--   Original derived finite annuity result. Contextual source page 110, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Without discount, assurance equals the probability mass that dies within the finite horizon.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bAssurancePV

namespace ActuarialAnnuities

theorem assurance_at_zero_interest (h : ℕ) (p : ℕ → ℝ) : bAssurancePV h 1 p = bTotal h p - p h := by sorry

end ActuarialAnnuities
