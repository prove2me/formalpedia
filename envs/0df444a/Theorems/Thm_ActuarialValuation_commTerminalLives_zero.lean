-- Prove2me | Theorems.Thm_ActuarialValuation_commTerminalLives_zero
-- name    : ActuarialValuation.commTerminalLives_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:11:52.170095+00:00
-- url     : https://prove2.me/theorems/bdd7d44b-21e1-4899-8ac9-7cfef8127aae
-- title:
--   Finite commutation functions: commTerminalLives_zero
-- statement:
--   At zero horizon the terminal survivors are the initially valued survivors. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   D_{x+0}=D_x
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commTerminalLives

namespace ActuarialValuation

theorem commTerminalLives_zero (l : ℕ → ℝ) (v : ℝ) (x : ℕ) : commTerminalLives l v x 0 = commDiscountedLives l v x := by sorry

end ActuarialValuation
