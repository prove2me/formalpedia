-- Prove2me | Theorems.Thm_Experiments_NSA_Approx_symm
-- name    : Experiments.NSA.Approx.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:50:47.457425+00:00
-- url     : https://prove2.me/theorems/7201228c-65ad-4add-9190-1bf33021ecc3
-- title:
--   Approx: symm
-- statement:
--   The Approx construction uses the symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L116-L118
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L116-L118

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem Experiments.NSA.Approx.symm {x y : Hyp E} (h : x ≈ₕ y) : y ≈ₕ x := by sorry
