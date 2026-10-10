-- Prove2me | Theorems.Thm_ActuarialValuation_commPureEndowment_cancel
-- name    : ActuarialValuation.commPureEndowment_cancel
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:18:43.400084+00:00
-- url     : https://prove2.me/theorems/aabbbdab-9dfb-424d-8c15-124b6f1b63aa
-- title:
--   Assurance and annuity monetary values: commPureEndowment_cancel
-- statement:
--   Pure endowment monetary value recovers the terminal discounted survivor count. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   ED_x=D_{x+n}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commTerminalLives
import Definitions.Def_actuarial_commPureEndowment

namespace ActuarialValuation

theorem commPureEndowment_cancel (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) (hD : commDiscountedLives l v x ≠ 0) : commPureEndowment l v x n * commDiscountedLives l v x = commTerminalLives l v x n := by sorry

end ActuarialValuation
