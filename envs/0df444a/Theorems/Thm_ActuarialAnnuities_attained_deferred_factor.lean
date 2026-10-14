-- Prove2me | Theorems.Thm_ActuarialAnnuities_attained_deferred_factor
-- name    : ActuarialAnnuities.attained_deferred_factor
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T20:10:43.600982+00:00
-- url     : https://prove2.me/theorems/14e9c336-e034-4e88-97a5-deda89076997
-- title:
--   Attained deferred factor
-- statement:
--   Deferred annuity equals discount times commencement survival times the conditional attained-age factor. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   V_{\text{deferred},0}=v^aS(a)V_{\text{conditional},a}
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Present value in GBP per unit nominal pension, with individual instalments in GBP, payment time in anniversaries and survival as dimensionless probability.
-- source:
--   Original derived finite annuity result. Contextual source page 157, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Deferred annuity equals discount times commencement survival times the conditional attained-age factor.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bSurvivalPV
import Definitions.Def_actuarial_bAttainedConditionalPV

namespace ActuarialAnnuities

theorem attained_deferred_factor (h a n delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) (ha : a+n ≤ h) (hs : 0 < bSurvival h p a) : bSurvivalPV h a n 0 delta v b p = v^a * bSurvival h p a * bAttainedConditionalPV h a n delta v b p := by sorry

end ActuarialAnnuities
