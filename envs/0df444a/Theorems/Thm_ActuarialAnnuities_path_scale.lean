-- Prove2me | Theorems.Thm_ActuarialAnnuities_path_scale
-- name    : ActuarialAnnuities.path_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:00:21.532183+00:00
-- url     : https://prove2.me/theorems/05ed4f36-db53-4014-aaa6-fda148674d28
-- title:
--   Path Scale
-- statement:
--   Every realised PV scales with the contractual instalment amount.
--
--   Mathematical relation:
--
--   $$
--   Z_{cb}(k)=cZ_b(k)
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 161, Increasing annuities (Chapter 5, section 5.10). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bPathPV

namespace ActuarialAnnuities

theorem path_scale (h a n g delta k : ℕ) (v c : ℝ) (b : ℕ → ℝ) : bPathPV h a n g delta v (fun j => c*b j) k = c*bPathPV h a n g delta v b k := by sorry

end ActuarialAnnuities
