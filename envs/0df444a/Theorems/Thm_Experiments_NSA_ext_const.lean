-- Prove2me | Theorems.Thm_Experiments_NSA_ext_const
-- name    : Experiments.NSA.ext_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:53:32.181704+00:00
-- url     : https://prove2.me/theorems/a2701bec-0822-4ee8-9d55-d791e7b77cc7
-- title:
--   NSA: ext const
-- statement:
--   The NSA construction uses the ext const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L60-L61
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L60-L61

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {α β γ : Type*}

theorem Experiments.NSA.ext_const (ξ : Hyp α) (c : β) : ext (fun _ => c) ξ = std c := by sorry
