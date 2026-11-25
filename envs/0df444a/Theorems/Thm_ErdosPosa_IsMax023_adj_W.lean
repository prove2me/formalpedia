-- Prove2me | Theorems.Thm_ErdosPosa_IsMax023_adj_W
-- name    : ErdosPosa.IsMax023.adj_W
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:29:08.650454+00:00
-- url     : https://prove2.me/theorems/b6318490-4ac4-52f4-a061-69ac9fcf670b
-- title:
--   Is Max023: adj W
-- statement:
--   Two distinct degree-2 vertices adjacent in `G` are adjacent in `H`.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMaximal.lean#L180-L193
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMaximal.lean#L180-L193

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

theorem ErdosPosa.IsMax023.adj_W (hH : IsMax023 G H) {w1 w2 : V} (hw1 : deg H w1 = 2)
    (hw2 : deg H w2 = 2) (hG : G.Adj w1 w2) : H.Adj w1 w2 := by sorry
