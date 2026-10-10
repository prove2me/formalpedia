-- Prove2me | Theorems.Thm_ActuarialValuation_commDiscountedLives_positive
-- name    : ActuarialValuation.commDiscountedLives_positive
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T23:17:22.480997+00:00
-- url     : https://prove2.me/theorems/6b22d68e-c97b-4326-9d9a-02e715c047e6
-- title:
--   Discounted life table functions: commDiscountedLives_positive
-- statement:
--   Positive initial cohort and discount factor ensure a nonzero valuation denominator. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   l_x,v>0\Rightarrow D_x>0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives

namespace ActuarialValuation

theorem commDiscountedLives_positive (l : ℕ → ℝ) (v : ℝ) (x : ℕ) (hl : 0 < l x) (hv : 0 < v) : 0 < commDiscountedLives l v x := by sorry

end ActuarialValuation
