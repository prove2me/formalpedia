-- Prove2me | Theorems.Thm_Experiments_NSA_Approx_sub_std
-- name    : Experiments.NSA.Approx.sub_std
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:54:09.654768+00:00
-- url     : https://prove2.me/theorems/8d555760-2a75-419c-8bd8-636d585b0330
-- title:
--   Approx: sub std
-- statement:
--   The Approx construction uses the sub std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L128-L131
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L128-L131

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem Experiments.NSA.Approx.sub_std {x y : Hyp E} {a b : E} (hx : x ≈ₕ std a) (hy : y ≈ₕ std b) :
    x - y ≈ₕ std (a - b) := by sorry
