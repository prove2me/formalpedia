-- Prove2me | Theorems.Thm_ActuarialAnnuities_assurance_annuity_complement
-- name    : ActuarialAnnuities.assurance_annuity_complement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:08:55.582255+00:00
-- url     : https://prove2.me/theorems/e48b39d7-38f8-4c45-b6a9-50abbee358e7
-- title:
--   Assurance annuity complement
-- statement:
--   Finite annual assurance and life-annuity-due complement retains the censored terminal mass. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   A^{(h)}+(1-v)\ddot a^{(h)}=M_h-v^hp_h
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Present value in GBP per unit nominal pension, with individual instalments in GBP, payment time in anniversaries and survival as dimensionless probability.
-- source:
--   Original derived finite annuity result. Contextual source page 110, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Finite annual assurance and life-annuity-due complement retains the censored terminal mass.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bSurvivalPV
import Definitions.Def_actuarial_bLevel
import Definitions.Def_actuarial_bAssurancePV

namespace ActuarialAnnuities

theorem assurance_annuity_complement (h : ℕ) (v : ℝ) (p : ℕ → ℝ) : bAssurancePV h v p + (1-v)*bSurvivalPV h 0 h 0 0 v (bLevel 1) p = bTotal h p - v^h*p h := by sorry

end ActuarialAnnuities
