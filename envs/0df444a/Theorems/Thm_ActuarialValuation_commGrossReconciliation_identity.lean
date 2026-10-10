-- Prove2me | Theorems.Thm_ActuarialValuation_commGrossReconciliation_identity
-- name    : ActuarialValuation.commGrossReconciliation_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:15:38.759784+00:00
-- url     : https://prove2.me/theorems/7b704151-b367-4e3c-b80a-040fed215ac9
-- title:
--   Finite commutation functions: commGrossReconciliation_identity
-- statement:
--   The full insurance-annuity-survival decomposition follows by telescoping annual differences. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   M_{x:n}+dN_{x:n}+D_{x+n}=D_x
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commGrossReconciliation

namespace ActuarialValuation

theorem commGrossReconciliation_identity (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) : commGrossReconciliation l v x n = commDiscountedLives l v x := by sorry

end ActuarialValuation
