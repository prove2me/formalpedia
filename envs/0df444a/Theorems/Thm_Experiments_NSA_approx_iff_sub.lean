-- Prove2me | Theorems.Thm_Experiments_NSA_approx_iff_sub
-- name    : Experiments.NSA.approx_iff_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:54:15.479105+00:00
-- url     : https://prove2.me/theorems/bde97320-e6db-4f5b-9644-7cb689915f27
-- title:
--   NSA: approx iff sub
-- statement:
--   The NSA construction uses the approx iff sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L124-L126
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L124-L126

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem Experiments.NSA.approx_iff_sub {x y : Hyp E} : x ≈ₕ y ↔ x - y ≈ₕ std 0 := by sorry
