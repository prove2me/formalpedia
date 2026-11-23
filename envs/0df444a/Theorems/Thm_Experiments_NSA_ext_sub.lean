-- Prove2me | Theorems.Thm_Experiments_NSA_ext_sub
-- name    : Experiments.NSA.ext_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:53:40.832206+00:00
-- url     : https://prove2.me/theorems/0427b888-ef70-4931-9006-c255ad90f2fd
-- title:
--   NSA: ext sub
-- statement:
--   The NSA construction uses the ext sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L66-L68
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L66-L68

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {α β γ : Type*}

theorem Experiments.NSA.ext_sub [Sub β] (f g : α → β) (ξ : Hyp α) :
    ext (fun x => f x - g x) ξ = ext f ξ - ext g ξ := by sorry
