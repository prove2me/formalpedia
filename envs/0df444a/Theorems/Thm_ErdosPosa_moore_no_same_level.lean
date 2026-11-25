-- Prove2me | Theorems.Thm_ErdosPosa_moore_no_same_level
-- name    : ErdosPosa.moore_no_same_level
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:22:15.66039+00:00
-- url     : https://prove2.me/theorems/931e0647-e032-46ab-8be8-0fc57c4bc5a6
-- title:
--   Erdos Posa: moore no same level
-- statement:
--   The Erdos Posa construction uses the moore no same level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMoore.lean#L81-L99
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMoore.lean#L81-L99

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

theorem ErdosPosa.moore_no_same_level {r : ℕ} (hno : ∀ S : Set V, S.ncard ≤ 2 * r + 1 → ¬ Cyc H S)
    {v x y : V} {d : ℕ} (hd : d ≤ r) (hx : H.Reachable v x) (hxd : H.dist v x = d)
    (hy : H.Reachable v y) (hyd : H.dist v y = d) (a : H.Adj x y) : False := by sorry
