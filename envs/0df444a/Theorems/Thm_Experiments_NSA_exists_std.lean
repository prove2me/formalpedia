-- Prove2me | Theorems.Thm_Experiments_NSA_exists_std
-- name    : Experiments.NSA.exists_std
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:54:40.500576+00:00
-- url     : https://prove2.me/theorems/70164bda-a725-4f2e-9243-d9d3a451bf8a
-- title:
--   NSA: exists std
-- statement:
--   In a proper space, a bounded element has a standard part, with the same bound: a bounded
--   sequence in a compact ball converges along the ultrafilter.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L160-L167
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L160-L167

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem Experiments.NSA.exists_std [ProperSpace E] {x : Hyp E} {C : ℝ} (hx : ext norm x ≤ std C) :
    ∃ a, ‖a‖ ≤ C ∧ x ≈ₕ std a := by sorry
