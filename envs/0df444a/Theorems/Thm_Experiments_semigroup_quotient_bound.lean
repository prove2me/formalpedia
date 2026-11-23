-- Prove2me | Theorems.Thm_Experiments_semigroup_quotient_bound
-- name    : Experiments.semigroup_quotient_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:53:06.887066+00:00
-- url     : https://prove2.me/theorems/e3349fce-8a85-4b27-a166-b30fe0d908c1
-- title:
--   Experiments: semigroup quotient bound
-- statement:
--   The Experiments construction uses the semigroup quotient bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/GeneratorBound.lean#L76-L97
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/GeneratorBound.lean#L76-L97

import Mathlib
import Definitions.Def_Experiments_GeneratorBound
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem Experiments.semigroup_quotient_bound (M : ℝ → A) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t)
    {δ : ℝ} (hδ : 0 < δ)
    (hnear : ∀ s ∈ Set.Icc 0 δ, ‖M s - 1‖ ≤ (1 / 2 : ℝ))
    {n : ℕ} (hn : 0 < n) :
    ‖(n : ℝ) • (M (δ / n) - 1)‖ ≤ 2 * ‖M δ - 1‖ := by sorry
