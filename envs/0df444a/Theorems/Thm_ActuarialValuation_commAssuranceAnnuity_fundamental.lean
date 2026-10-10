-- Prove2me | Theorems.Thm_ActuarialValuation_commAssuranceAnnuity_fundamental
-- name    : ActuarialValuation.commAssuranceAnnuity_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:33:28.477092+00:00
-- url     : https://prove2.me/theorems/d35ecbf9-d236-47d6-a74c-d6dd0d2a0dac
-- title:
--   Assurance and annuity monetary values: commAssuranceAnnuity_fundamental
-- statement:
--   The capstone establishes both raw and conditional actuarial valuation identities and nonnegativity of term assurance and pure endowment for a valid life table. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   M+dN+D_{x+n}=D_x,\quad A+d\ddot a+E=1
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commGrossReconciliation
import Definitions.Def_actuarial_commTermAssurance
import Definitions.Def_actuarial_commPureEndowment
import Definitions.Def_actuarial_commLifeValueBalance

namespace ActuarialValuation

theorem commAssuranceAnnuity_fundamental (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) (hv : 0 < v) (hl : 0 < l x) (hdec : ∀ k ∈ Finset.range n, l (x+k+1) ≤ l (x+k)) (hnonneg : 0 ≤ l (x+n)) : (commGrossReconciliation l v x n = commDiscountedLives l v x) ∧ (commLifeValueBalance l v x n = 1) ∧ (0 ≤ commTermAssurance l v x n) ∧ (0 ≤ commPureEndowment l v x n) := by sorry

end ActuarialValuation
