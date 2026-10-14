-- Prove2me | Theorems.Thm_ActuarialAnnuities_path_add
-- name    : ActuarialAnnuities.path_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:00:34.046072+00:00
-- url     : https://prove2.me/theorems/820c7872-9206-4432-8341-4622ec833775
-- title:
--   Path Add
-- statement:
--   Independent streams add at every lifetime state before expectation.
--
--   Mathematical relation:
--
--   $$
--   Z_{b+c}(k)=Z_b(k)+Z_c(k)
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 161, Increasing annuities (Chapter 5, section 5.10). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bPathPV

namespace ActuarialAnnuities

theorem path_add (h a n g delta k : ℕ) (v : ℝ) (b c : ℕ → ℝ) : bPathPV h a n g delta v (fun j => b j+c j) k = bPathPV h a n g delta v b k+bPathPV h a n g delta v c k := by sorry

end ActuarialAnnuities
