-- Prove2me | Theorems.Thm_ActuarialValuation_commTerminalLives_succ
-- name    : ActuarialValuation.commTerminalLives_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:14:41.320687+00:00
-- url     : https://prove2.me/theorems/0d58e944-c776-4075-bf59-16c2c63ed195
-- title:
--   Finite commutation functions: commTerminalLives_succ
-- statement:
--   Extended term moves the terminal survival date by exactly one year. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   D_{x+n+1}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commTerminalLives

namespace ActuarialValuation

theorem commTerminalLives_succ (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) : commTerminalLives l v x (n+1) = commDiscountedLives l v (x+n+1) := by sorry

end ActuarialValuation
