-- Prove2me | Theorems.Thm_ErdosPosa_IsMax023_no_cyc_R
-- name    : ErdosPosa.IsMax023.no_cyc_R
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:29:29.05451+00:00
-- url     : https://prove2.me/theorems/b6bd2302-3bf4-47f1-b991-2b874a3b6b34
-- title:
--   Is Max023: no cyc R
-- statement:
--   `G` has no cycle among the vertices missed by `H`.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMaximal.lean#L80-L113
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMaximal.lean#L80-L113

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Definitions.Def_ErdosPosaLib_EPMaximal
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable [Finite V] {G H : SimpleGraph V}

theorem ErdosPosa.IsMax023.no_cyc_R (hH : IsMax023 G H) : ¬ Cyc G {v | deg H v = 0} := by sorry
