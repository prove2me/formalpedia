-- Prove2me | Theorems.Thm_Experiments_exists_bounded_generators
-- name    : Experiments.exists_bounded_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:52:55.185108+00:00
-- url     : https://prove2.me/theorems/db9a706b-fd24-414f-8d61-d5a2a0ea741f
-- title:
--   Experiments: exists bounded generators
-- statement:
--   The difference quotients along `h = δ / (n + 1)` are bounded.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/GeneratorBound.lean#L100-L122
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/GeneratorBound.lean#L100-L122

import Mathlib
import Definitions.Def_Experiments_GeneratorBound
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem Experiments.exists_bounded_generators (M : ℝ → A)
    (hcont : ContinuousWithinAt M (Set.Ici 0) 0) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t) :
    ∃ δ > 0, ∃ C : ℝ, ∀ n : ℕ,
      ‖(δ / (n + 1 : ℝ))⁻¹ • (M (δ / (n + 1 : ℝ)) - 1)‖ ≤ C := by sorry
