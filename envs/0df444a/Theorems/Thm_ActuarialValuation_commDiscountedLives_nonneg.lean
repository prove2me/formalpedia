-- Prove2me | Theorems.Thm_ActuarialValuation_commDiscountedLives_nonneg
-- name    : ActuarialValuation.commDiscountedLives_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:05:52.950018+00:00
-- url     : https://prove2.me/theorems/b9de01b0-5a2f-4ec0-9f9e-a5ddaaceeb2b
-- title:
--   Discounted life table functions: commDiscountedLives_nonneg
-- statement:
--   Nonnegative survival and discount weights yield nonnegative discounted lives. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   l_x,v\ge0\Rightarrow D_x\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives

namespace ActuarialValuation

theorem commDiscountedLives_nonneg (l : ℕ → ℝ) (v : ℝ) (x : ℕ) (hl : 0 ≤ l x) (hv : 0 ≤ v) : 0 ≤ commDiscountedLives l v x := by sorry

end ActuarialValuation
