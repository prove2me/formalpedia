-- Prove2me | Theorems.Thm_ActuarialValuation_commPureEndowment_zero
-- name    : ActuarialValuation.commPureEndowment_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:16:24.950737+00:00
-- url     : https://prove2.me/theorems/d0ab09f8-9609-4afa-b5d1-a03980ab07a6
-- title:
--   Assurance and annuity monetary values: commPureEndowment_zero
-- statement:
--   Unit payable immediately on survival has unit monetary value. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   E_{x:0}=1
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commPureEndowment

namespace ActuarialValuation

theorem commPureEndowment_zero (l : ℕ → ℝ) (v : ℝ) (x : ℕ) (h : commDiscountedLives l v x ≠ 0) : commPureEndowment l v x 0 = 1 := by sorry

end ActuarialValuation
