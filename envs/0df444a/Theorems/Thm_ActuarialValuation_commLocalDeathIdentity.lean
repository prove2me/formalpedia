-- Prove2me | Theorems.Thm_ActuarialValuation_commLocalDeathIdentity
-- name    : ActuarialValuation.commLocalDeathIdentity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:07:25.425924+00:00
-- url     : https://prove2.me/theorems/7e444333-b20a-47bb-ba09-2c8142de25c8
-- title:
--   Discounted life table functions: commLocalDeathIdentity
-- statement:
--   One-year death and annuity-discount value telescope to the discounted decrement. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   C_x+(1-v)D_x=D_x-D_{x+1}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commDiscountedDeaths
import Definitions.Def_actuarial_commEffectiveDiscount

namespace ActuarialValuation

theorem commLocalDeathIdentity (l : ℕ → ℝ) (v : ℝ) (x : ℕ) : commDiscountedDeaths l v x + commEffectiveDiscount v * commDiscountedLives l v x = commDiscountedLives l v x - commDiscountedLives l v (x+1) := by sorry

end ActuarialValuation
