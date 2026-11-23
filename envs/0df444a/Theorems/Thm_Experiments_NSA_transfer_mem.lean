-- Prove2me | Theorems.Thm_Experiments_NSA_transfer_mem
-- name    : Experiments.NSA.transfer_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:53:51.049742+00:00
-- url     : https://prove2.me/theorems/300f7640-dcc0-4525-9b42-9ac0ee03f99f
-- title:
--   NSA: transfer mem
-- statement:
--   Transfer: `∀ x ∈ s, f x ∈ t` gives `∀ ξ ∈ *s, *f ξ ∈ *t`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L78-L81
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L78-L81

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {α β γ : Type*}

theorem Experiments.NSA.transfer_mem {f : α → β} {s : Set α} {t : Set β} (h : ∀ x ∈ s, f x ∈ t) {ξ : Hyp α}
    (hξ : IMem ξ s) : IMem (ext f ξ) t := by sorry
