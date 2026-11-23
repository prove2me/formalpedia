-- Prove2me | Theorems.Thm_Experiments_NSA_transfer_eq
-- name    : Experiments.NSA.transfer_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:54:02.058703+00:00
-- url     : https://prove2.me/theorems/53aba361-dcb1-40e5-8d0d-6f4e1e993d3a
-- title:
--   NSA: transfer eq
-- statement:
--   Transfer: `∀ x ∈ s, f x = g x` gives `∀ ξ ∈ *s, *f ξ = *g ξ`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L90-L93
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L90-L93

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {α β γ : Type*}

theorem Experiments.NSA.transfer_eq {f g : α → β} {s : Set α} (h : ∀ x ∈ s, f x = g x) {ξ : Hyp α}
    (hξ : IMem ξ s) : ext f ξ = ext g ξ := by sorry
