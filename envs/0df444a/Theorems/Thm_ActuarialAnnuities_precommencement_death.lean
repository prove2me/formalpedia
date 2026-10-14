-- Prove2me | Theorems.Thm_ActuarialAnnuities_precommencement_death
-- name    : ActuarialAnnuities.precommencement_death
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T19:59:38.009021+00:00
-- url     : https://prove2.me/theorems/24e81333-1092-4e69-b6bc-c12f6d8b5645
-- title:
--   Precommencement Death
-- statement:
--   Death before deferred commencement prevents guarantee activation.
--
--   Mathematical relation:
--
--   $$
--   k<a\Longrightarrow Z_k=0
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 159, Guaranteed annuities (Chapter 5, section 5.9). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bPathPV

namespace ActuarialAnnuities

theorem precommencement_death (h a n g delta k : ℕ) (v : ℝ) (b : ℕ → ℝ) (hk : k < a) : bPathPV h a n g delta v b k = 0 := by sorry

end ActuarialAnnuities
