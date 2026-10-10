-- Prove2me | Theorems.Thm_ActuarialValuation_commTemporaryAnnuity_cancel
-- name    : ActuarialValuation.commTemporaryAnnuity_cancel
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:17:21.371728+00:00
-- url     : https://prove2.me/theorems/0f6e75e0-3b8d-4ecd-96af-4af90d5c6930
-- title:
--   Assurance and annuity monetary values: commTemporaryAnnuity_cancel
-- statement:
--   Multiplying conditional annuity PV by the starting discounted lives recovers N. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \ddot aD_x=N
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commSurvivorSum
import Definitions.Def_actuarial_commTemporaryAnnuity

namespace ActuarialValuation

theorem commTemporaryAnnuity_cancel (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) (hD : commDiscountedLives l v x ≠ 0) : commTemporaryAnnuity l v x n * commDiscountedLives l v x = commSurvivorSum l v x n := by sorry

end ActuarialValuation
