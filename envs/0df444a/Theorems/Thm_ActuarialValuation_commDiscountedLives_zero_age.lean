-- Prove2me | Theorems.Thm_ActuarialValuation_commDiscountedLives_zero_age
-- name    : ActuarialValuation.commDiscountedLives_zero_age
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T23:17:02.420986+00:00
-- url     : https://prove2.me/theorems/57ec72fb-fbd6-4c1f-a9d2-abf71327031c
-- title:
--   Discounted life table functions: commDiscountedLives_zero_age
-- statement:
--   No discount accrues at age zero. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   D_0=l_0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives

namespace ActuarialValuation

theorem commDiscountedLives_zero_age (l : ℕ → ℝ) (v : ℝ) : commDiscountedLives l v 0 = l 0 := by sorry

end ActuarialValuation
