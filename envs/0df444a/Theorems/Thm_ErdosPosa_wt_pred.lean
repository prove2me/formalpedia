-- Prove2me | Theorems.Thm_ErdosPosa_wt_pred
-- name    : ErdosPosa.wt_pred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:26:22.269805+00:00
-- url     : https://prove2.me/theorems/f09caf09-7e23-59dc-bbcd-f0e721f12ef9
-- title:
--   Erdos Posa: wt pred
-- statement:
--   The Erdos Posa construction uses the wt pred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L46-L47
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L46-L47

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.wt_pred (d : ℕ) (hd : 1 ≤ d) : wt d ≤ wt (d - 1) + 1 := by sorry
