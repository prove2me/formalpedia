-- Prove2me | Theorems.Thm_ActuarialValuation_commAnnualDeaths_nonneg
-- name    : ActuarialValuation.commAnnualDeaths_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:06:05.730834+00:00
-- url     : https://prove2.me/theorems/fc1ad096-6613-4c2c-9d2d-13cfeb2d2cde
-- title:
--   Discounted life table functions: commAnnualDeaths_nonneg
-- statement:
--   Valid cohort life table has nonnegative deaths. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   l_{x+1}\le l_x\Rightarrow d_x\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commAnnualDeaths

namespace ActuarialValuation

theorem commAnnualDeaths_nonneg (l : ℕ → ℝ) (x : ℕ) (h : l (x+1) ≤ l x) : 0 ≤ commAnnualDeaths l x := by sorry

end ActuarialValuation
