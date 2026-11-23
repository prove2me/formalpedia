-- Prove2me | Theorems.Thm_Experiments_geometric_average_near_one
-- name    : Experiments.geometric_average_near_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:52:58.0992+00:00
-- url     : https://prove2.me/theorems/1ece3da9-edfc-4def-b2a7-ff47e570c5b1
-- title:
--   Experiments: geometric average near one
-- statement:
--   The Experiments construction uses the geometric average near one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/GeneratorBound.lean#L32-L50
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/GeneratorBound.lean#L32-L50

import Mathlib
import Definitions.Def_Experiments_GeneratorBound
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem Experiments.geometric_average_near_one (x : A) {n : ℕ} (hn : 0 < n)
    (hx : ∀ k ∈ Finset.range n, ‖x ^ k - 1‖ ≤ (1 / 2 : ℝ)) :
    ‖(n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, x ^ k) - 1‖ ≤ (1 / 2 : ℝ) := by sorry
