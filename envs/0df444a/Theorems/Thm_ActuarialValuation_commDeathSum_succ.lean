-- Prove2me | Theorems.Thm_ActuarialValuation_commDeathSum_succ
-- name    : ActuarialValuation.commDeathSum_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:11:05.44585+00:00
-- url     : https://prove2.me/theorems/b4bead46-67d2-4137-b37e-49662506546f
-- title:
--   Finite commutation functions: commDeathSum_succ
-- statement:
--   Term assurance valuation adds one year's discounted death claims. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   M_{x:n+1}=M_{x:n}+C_{x+n}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedDeaths
import Definitions.Def_actuarial_commDeathSum

namespace ActuarialValuation

theorem commDeathSum_succ (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) : commDeathSum l v x (n+1) = commDeathSum l v x n + commDiscountedDeaths l v (x+n) := by sorry

end ActuarialValuation
