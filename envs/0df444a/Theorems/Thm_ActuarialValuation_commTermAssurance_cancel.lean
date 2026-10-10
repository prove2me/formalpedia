-- Prove2me | Theorems.Thm_ActuarialValuation_commTermAssurance_cancel
-- name    : ActuarialValuation.commTermAssurance_cancel
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:17:36.847787+00:00
-- url     : https://prove2.me/theorems/8bf00773-2563-4dbf-94c7-934d97cd6e24
-- title:
--   Assurance and annuity monetary values: commTermAssurance_cancel
-- statement:
--   Multiplying conditional term assurance value by starting discounted lives recovers M. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   AD_x=M
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commDeathSum
import Definitions.Def_actuarial_commTermAssurance

namespace ActuarialValuation

theorem commTermAssurance_cancel (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) (hD : commDiscountedLives l v x ≠ 0) : commTermAssurance l v x n * commDiscountedLives l v x = commDeathSum l v x n := by sorry

end ActuarialValuation
