-- Prove2me | Theorems.Thm_Experiments_NSA_ext_mul
-- name    : Experiments.NSA.ext_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:53:44.830373+00:00
-- url     : https://prove2.me/theorems/fc83b34e-f974-42c7-818a-1735491f8605
-- title:
--   NSA: ext mul
-- statement:
--   The NSA construction uses the ext mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L70-L72
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Ultrapower.lean#L70-L72

import Mathlib
import Definitions.Def_Experiments_Ultrapower
set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {α β γ : Type*}

theorem Experiments.NSA.ext_mul [Mul β] (f g : α → β) (ξ : Hyp α) :
    ext (fun x => f x * g x) ξ = ext f ξ * ext g ξ := by sorry
