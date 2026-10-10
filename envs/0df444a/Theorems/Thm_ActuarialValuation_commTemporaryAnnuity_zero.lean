-- Prove2me | Theorems.Thm_ActuarialValuation_commTemporaryAnnuity_zero
-- name    : ActuarialValuation.commTemporaryAnnuity_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:15:56.050744+00:00
-- url     : https://prove2.me/theorems/3acc0154-168a-43b6-b563-1062190be668
-- title:
--   Assurance and annuity monetary values: commTemporaryAnnuity_zero
-- statement:
--   A temporary annuity of zero payments is worthless. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \ddot a_{x:0}=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commTemporaryAnnuity

namespace ActuarialValuation

theorem commTemporaryAnnuity_zero (l : ℕ → ℝ) (v : ℝ) (x : ℕ) : commTemporaryAnnuity l v x 0 = 0 := by sorry

end ActuarialValuation
