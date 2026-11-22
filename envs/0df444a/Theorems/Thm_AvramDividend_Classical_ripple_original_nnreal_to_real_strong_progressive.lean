-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_original_nnreal_to_real_strong_progressive
-- name    : AvramDividend.Classical.ripple_original_nnreal_to_real_strong_progressive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:45:04.288887+00:00
-- url     : https://prove2.me/theorems/4c7145bd-ac1a-4ee3-bf88-c3135521f58b
-- title:
--   Exact right-continuous filtration real-time pullback preserves strong progressive measurability
-- statement:
--   For any original filtration on nonnegative time, and any real-time filtration whose sigma-algebra at t equals the original sigma-algebra at max(t,0), every strongly progressively measurable original nonnegative-time process remains strongly progressively measurable when indexed by real time through Real.toNNReal. The same sample space and filtration at each corresponding time are preserved. This is the missing time-indexed interface for the imported LevyStochCalc Brownian stochastic integral in Avram.
-- source:
--   Pinned Mathlib IsStronglyProgressive on products Iic t times original sample space, monotonicity and measurability of Real.toNNReal, and original Proved zerojump filtered Brownian bridge e72d0175-b6bd-45bf-ad30-0049fa7ed69a.

import Mathlib
open MeasureTheory Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.ripple_original_nnreal_to_real_strong_progressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) (Fr : Filtration ℝ mΩ)
    (hFr : ∀ t : ℝ, Fr t = F (Real.toNNReal t))
    (G : ℝ≥0 → Ω → ℝ)
    (hG : IsStronglyProgressive F G) :
    IsStronglyProgressive Fr
      (fun t ω => G (Real.toNNReal t) ω) := by sorry
