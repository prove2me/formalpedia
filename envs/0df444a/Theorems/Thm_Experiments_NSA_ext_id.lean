-- Prove2me | Theorems.Thm_Experiments_NSA_ext_id
-- name    : Experiments.NSA.ext_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:53:39.570063+00:00
-- url     : https://prove2.me/theorems/921330f7-9427-484c-ab0f-4978e9e88f5d
-- title:
--   NSA: ext id
-- statement:
--   The NSA construction uses the ext id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L63-L64
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L63-L64

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {α β γ : Type*}

theorem Experiments.NSA.ext_id (ξ : Hyp α) : ext (fun x => x) ξ = ξ := by sorry
