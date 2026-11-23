-- Prove2me | Theorems.Thm_Experiments_geometric_quotient_bound
-- name    : Experiments.geometric_quotient_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:52:54.479078+00:00
-- url     : https://prove2.me/theorems/7c702a07-afca-4328-9709-dbd833205d1d
-- title:
--   Experiments: geometric quotient bound
-- statement:
--   The Experiments construction uses the geometric quotient bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/GeneratorBound.lean#L52-L74
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/GeneratorBound.lean#L52-L74

import Mathlib
import Definitions.Def_Experiments_GeneratorBound
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem Experiments.geometric_quotient_bound (x : A) {n : ℕ} (hn : 0 < n)
    (hx : ‖(n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, x ^ k) - 1‖ ≤ (1 / 2 : ℝ)) :
    ‖(n : ℝ) • (x - 1)‖ ≤ 2 * ‖x ^ n - 1‖ := by sorry
