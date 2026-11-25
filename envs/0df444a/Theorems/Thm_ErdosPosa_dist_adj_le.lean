-- Prove2me | Theorems.Thm_ErdosPosa_dist_adj_le
-- name    : ErdosPosa.dist_adj_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:21:48.64787+00:00
-- url     : https://prove2.me/theorems/159018f8-3777-47a9-a4d4-662d244fad04
-- title:
--   Erdos Posa: dist adj le
-- statement:
--   The Erdos Posa construction uses the dist adj le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMoore.lean#L40-L44
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMoore.lean#L40-L44

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Definitions.Def_ErdosPosaLib_EPMoore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*} {H : SimpleGraph V}

theorem ErdosPosa.dist_adj_le {v x y : V} (hx : H.Reachable v x) (hxy : H.Adj x y) :
    H.dist v y ≤ H.dist v x + 1 := by sorry
