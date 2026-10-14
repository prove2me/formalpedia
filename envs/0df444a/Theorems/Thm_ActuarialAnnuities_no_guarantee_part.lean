-- Prove2me | Theorems.Thm_ActuarialAnnuities_no_guarantee_part
-- name    : ActuarialAnnuities.no_guarantee_part
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:02:10.790084+00:00
-- url     : https://prove2.me/theorems/7e65c53d-5867-460b-a0a1-e65c92b0b05d
-- title:
--   No Guarantee Part
-- statement:
--   Zero guaranteed instalments leave no guaranteed present-value component.
--
--   Mathematical relation:
--
--   $$
--   g=0\Longrightarrow V_{\text{guaranteed}}=0
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 159, Guaranteed annuities (Chapter 5, section 5.9). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bGuaranteedPV

namespace ActuarialAnnuities

theorem no_guarantee_part (h a n delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : bGuaranteedPV h a n 0 delta v b p = 0 := by sorry

end ActuarialAnnuities
