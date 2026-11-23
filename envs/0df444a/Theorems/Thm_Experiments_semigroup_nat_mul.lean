-- Prove2me | Theorems.Thm_Experiments_semigroup_nat_mul
-- name    : Experiments.semigroup_nat_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:52:49.896568+00:00
-- url     : https://prove2.me/theorems/b9880adf-62fc-4b3a-b3ed-f13e67490e95
-- title:
--   Experiments: semigroup nat mul
-- statement:
--   The Experiments construction uses the semigroup nat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/GeneratorBound.lean#L20-L28
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/GeneratorBound.lean#L20-L28

import Mathlib
import Definitions.Def_Experiments_GeneratorBound
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments

theorem Experiments.semigroup_nat_mul {E : Type*} [Monoid E] (M : ℝ → E) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t)
    {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    M ((n : ℝ) * h) = M h ^ n := by sorry
