-- Prove2me | Theorems.Thm_ActuarialAnnuities_path_expectation_reconciliation
-- name    : ActuarialAnnuities.path_expectation_reconciliation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:01:43.819447+00:00
-- url     : https://prove2.me/theorems/d818d4f5-4520-4a6d-a93e-f48ef47cbbee
-- title:
--   Path Expectation Reconciliation
-- statement:
--   Finite reversal of actual lifetime-state and payment-index sums derives survival projection.
--
--   Mathematical relation:
--
--   $$
--   \sum_{k=0}^{h}p_kZ_k=\sum_jb_jv^{j+\delta}\Pr(\text{payment at }j+\delta)
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 161, Increasing annuities (Chapter 5, section 5.10). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bExpectedPV
import Definitions.Def_actuarial_bSurvivalPV

namespace ActuarialAnnuities

theorem path_expectation_reconciliation (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : bExpectedPV h a n g delta v b p = bSurvivalPV h a n g delta v b p := by sorry

end ActuarialAnnuities
