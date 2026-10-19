-- Prove2me | Theorems.Thm_Continuous_positive_iff_positive_on_neighborhood
-- name    : Continuous.positive_iff_positive_on_neighborhood
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:04.614989+00:00
-- url     : https://prove2.me/theorems/4627df4d-0fb1-45f0-85bf-1db7b1961b9e
-- title:
--   Continuous.positive_iff_positive_on_neighborhood
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
variable {E : Type*} [TopologicalSpace E]

theorem Continuous.positive_iff_positive_on_neighborhood {f : E → ℝ} (hf₁ : Continuous f) (x : E) :
  0 < f x ↔ ∃ U ∈ (nhds x), ∀ y ∈ U, 0 < f y := by sorry
