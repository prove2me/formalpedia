-- Prove2me | Theorems.Thm_Experiments_NSA_Approx_mul_std
-- name    : Experiments.NSA.Approx.mul_std
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:54:22.377065+00:00
-- url     : https://prove2.me/theorems/f8a864e6-37f1-4fc7-8ce8-f9624f31006e
-- title:
--   Approx: mul std
-- statement:
--   The Approx construction uses the mul std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L133-L136
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L133-L136

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem Experiments.NSA.Approx.mul_std {R : Type*} [NormedRing R] {x y : Hyp R} {a b : R}
    (hx : x ≈ₕ std a) (hy : y ≈ₕ std b) : x * y ≈ₕ std (a * b) := by sorry
