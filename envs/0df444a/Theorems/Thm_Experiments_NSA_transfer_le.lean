-- Prove2me | Theorems.Thm_Experiments_NSA_transfer_le
-- name    : Experiments.NSA.transfer_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:53:55.101379+00:00
-- url     : https://prove2.me/theorems/0b7210b7-e8c4-47df-8e64-67a579258a48
-- title:
--   NSA: transfer le
-- statement:
--   Transfer: `∀ x ∈ s, f x ≤ g x` gives `∀ ξ ∈ *s, *f ξ ≤ *g ξ`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L84-L87
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L84-L87

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {α β γ : Type*}

theorem Experiments.NSA.transfer_le {f g : α → ℝ} {s : Set α} (h : ∀ x ∈ s, f x ≤ g x) {ξ : Hyp α}
    (hξ : IMem ξ s) : ext f ξ ≤ ext g ξ := by sorry
