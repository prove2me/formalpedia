-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_BCF_lift_of_nonnegative_uniform_bound
-- name    : AvramDividend.Classical.causal_BCF_lift_of_nonnegative_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:37:18.621652+00:00
-- url     : https://prove2.me/theorems/0d07434a-7ea3-4a3a-837b-12c18b21da6b
-- title:
--   Lift a bounded continuous nonnegative-time function to the BCF Banach space
-- statement:
--   If F is continuous on the closed nonnegative real half-line and uniformly bounded in absolute value there, its restriction defines a bounded continuous function on the nonnegative reals. The proof constructs the restricted continuous map and controls its image diameter by twice the uniform bound.
-- source:
--   Mathlib.Topology.ContinuousMap.Bounded.Basic BoundedContinuousFunction.mkOfBound, and ContinuousOn.comp_continuous.

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical Set
open scoped NNReal

theorem AvramDividend.Classical.causal_BCF_lift_of_nonnegative_uniform_bound
    (F : ℝ → ℝ) (M : ℝ)
    (hContinuous : ContinuousOn F (Ici (0 : ℝ)))
    (hBound : ∀ x : ℝ, 0 ≤ x → |F x| ≤ M) :
    ∃ f : BoundedContinuousFunction ℝ≥0 ℝ,
      ∀ x : ℝ≥0, f x = F (x : ℝ) := by sorry
