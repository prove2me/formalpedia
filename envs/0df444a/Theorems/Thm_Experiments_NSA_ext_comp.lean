-- Prove2me | Theorems.Thm_Experiments_NSA_ext_comp
-- name    : Experiments.NSA.ext_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:53:29.402852+00:00
-- url     : https://prove2.me/theorems/66bb74c9-6c56-4f29-b22c-14d86661f530
-- title:
--   NSA: ext comp
-- statement:
--   The NSA construction uses the ext comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L56-L58
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L56-L58

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {α β γ : Type*}

theorem Experiments.NSA.ext_comp (f : β → γ) (g : α → β) (ξ : Hyp α) :
    ext f (ext g ξ) = ext (fun x => f (g x)) ξ := by sorry
