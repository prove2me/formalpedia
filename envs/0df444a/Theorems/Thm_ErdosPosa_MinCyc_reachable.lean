-- Prove2me | Theorems.Thm_ErdosPosa_MinCyc_reachable
-- name    : ErdosPosa.MinCyc.reachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:20:50.848367+00:00
-- url     : https://prove2.me/theorems/df39969f-e0d7-4583-950e-83597ab32cbb
-- title:
--   Min Cyc: reachable
-- statement:
--   The Min Cyc construction uses the reachable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L291-L319
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPCyc.lean#L291-L319

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.MinCyc.reachable {H : SimpleGraph V} {T : Set V} (h : MinCyc H T) {a b : V} (ha : a ∈ T)
    (hb : b ∈ T) : (restr H T).Reachable a b := by sorry
