-- Prove2me | Theorems.Thm_Experiments_NSA_approx_ext_of_continuousWithinAt
-- name    : Experiments.NSA.approx_ext_of_continuousWithinAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:54:37.634251+00:00
-- url     : https://prove2.me/theorems/9531530e-5a93-4960-9944-a0017eab8fb8
-- title:
--   NSA: approx ext of continuous Within At
-- statement:
--   Continuity: points of `*s` infinitely close to `x` map to points infinitely close to
--   `f x`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L171-L177
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L171-L177

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem Experiments.NSA.approx_ext_of_continuousWithinAt {f : F → E} {s : Set F} {x : F}
    (hf : ContinuousWithinAt f s x) {ξ : Hyp F} (hξs : IMem ξ s) (hξ : ξ ≈ₕ std x) :
    ext f ξ ≈ₕ std (f x) := by sorry
