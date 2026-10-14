-- Prove2me | Theorems.Thm_ActuarialAnnuities_root_full_reconciliation_v2
-- name    : ActuarialAnnuities.root_full_reconciliation_v2
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T20:13:47.146504+00:00
-- url     : https://prove2.me/theorems/eda5b7df-638a-4350-9b8f-996dbe64fdee
-- title:
--   Complete single-life annuity valuation across timing, estate guarantees, UDD and moments
-- statement:
--   A unified source-of-truth cashflow capstone connects actual expected PV, estate guarantee, second moment, terminal assurance and real UDD micro-states. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[Z]=V,\quad \mathbb E[Z^2]=M_2,\quad V=V_g+V_{\text{post}},\quad A^{(h)}+(1-v)\ddot a^{(h)}=1-v^hp_h
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Present values in GBP, second moments in GBP², state masses and survival in dimensionless probabilities; annual and micro-period discount factors are dimensionless.
-- source:
--   Original derived finite annuity result. Contextual source page 143, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. A unified source-of-truth cashflow capstone connects actual expected PV, estate guarantee, second moment, terminal assurance and real UDD micro-states.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bExpectedPV
import Definitions.Def_actuarial_bSurvivalPV
import Definitions.Def_actuarial_bGuaranteedPV
import Definitions.Def_actuarial_bPostGuaranteePV
import Definitions.Def_actuarial_bLevel
import Definitions.Def_actuarial_bSecondMoment
import Definitions.Def_actuarial_bAssurancePV
import Definitions.Def_actuarial_bProjectedSecondMoment
import Definitions.Def_actuarial_bFractionalExpectedPV
import Definitions.Def_actuarial_bFractionalSurvivalPV

namespace ActuarialAnnuities

theorem root_full_reconciliation_v2 (h a n g m : ℕ) (v w : ℝ) (b p : ℕ → ℝ) (hp : bTotal h p = 1) (hn : ∀ k, 0 ≤ p k) (hv : 0 < v) (hv1 : v ≤ 1) (hw : 0 < w) (hm : 0 < m) : (bExpectedPV h a n g 0 v b p = bSurvivalPV h a n g 0 v b p) ∧ (bExpectedPV h a n g 1 v b p = bSurvivalPV h a n g 1 v b p) ∧ (bSurvivalPV h a n g 0 v b p = bGuaranteedPV h a n g 0 v b p+bPostGuaranteePV h a n g 0 v b p) ∧ (bSecondMoment h a n g 0 v b p = bProjectedSecondMoment h a n g 0 v b p) ∧ (bAssurancePV h v p+(1-v)*bSurvivalPV h 0 h 0 0 v (bLevel 1) p = 1-v^h*p h) ∧ (bFractionalExpectedPV h a n g 0 m w b p = bFractionalSurvivalPV h a n g 0 m w b p) := by sorry

end ActuarialAnnuities
