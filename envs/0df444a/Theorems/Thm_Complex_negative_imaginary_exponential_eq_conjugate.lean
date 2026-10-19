-- Prove2me | Theorems.Thm_Complex_negative_imaginary_exponential_eq_conjugate
-- name    : Complex.negative_imaginary_exponential_eq_conjugate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:04.614989+00:00
-- url     : https://prove2.me/theorems/bdb208d9-9ffe-4912-b6a7-f9d8867e4327
-- title:
--   Complex.negative_imaginary_exponential_eq_conjugate
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable {d : ℕ} [Fact (0 < d)]
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
noncomputable section
open scoped BigOperators FourierTransform
omit [Fact (0 < d)]

theorem Complex.negative_imaginary_exponential_eq_conjugate (x m : EuclideanSpace ℝ (Fin d)) :
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (⟪x, m⟫_[ℝ] : ℂ))) =
    (starRingEnd ℂ) (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (⟪x, m⟫_[ℝ] : ℂ))) := by sorry
