-- Prove2me | Theorems.Thm_Continuous_nonnegative_integral_vanishes_iff_function_vanishes
-- name    : Continuous.nonnegative_integral_vanishes_iff_function_vanishes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:04.614989+00:00
-- url     : https://prove2.me/theorems/c24b8715-ac3b-4bdc-873c-68d0899cc30b
-- title:
--   Continuous.nonnegative_integral_vanishes_iff_function_vanishes
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
open MeasureTheory Filter
variable {E : Type*} [NormedAddCommGroup E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [MeasureSpace E] [BorelSpace E]
variable [(volume : Measure E).IsAddLeftInvariant] [(volume : Measure E).Regular]
  [NeZero (volume : Measure E)]

theorem Continuous.nonnegative_integral_vanishes_iff_function_vanishes {f : E → ℝ} (hf₁ : Continuous f)
  (hf₂ : Integrable f) (hnn : ∀ x, 0 ≤ f x) : ∫ (v : E), f v = 0 ↔ f = 0 := by sorry
