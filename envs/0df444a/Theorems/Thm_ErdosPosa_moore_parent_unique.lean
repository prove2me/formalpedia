-- Prove2me | Theorems.Thm_ErdosPosa_moore_parent_unique
-- name    : ErdosPosa.moore_parent_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:21:34.341351+00:00
-- url     : https://prove2.me/theorems/fcd13e04-1a17-5fe9-87c3-ceb362320bb7
-- title:
--   Erdos Posa: moore parent unique
-- statement:
--   The Erdos Posa construction uses the moore parent unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMoore.lean#L52-L79
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMoore.lean#L52-L79

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

theorem ErdosPosa.moore_parent_unique {r : ℕ} (hno : ∀ S : Set V, S.ncard ≤ 2 * r + 1 → ¬ Cyc H S)
    {v x p1 p2 : V} {d : ℕ} (hd : d + 1 ≤ r) (h1 : H.Reachable v p1) (h1d : H.dist v p1 = d)
    (h2 : H.Reachable v p2) (h2d : H.dist v p2 = d) (hx : H.dist v x = d + 1)
    (a1 : H.Adj x p1) (a2 : H.Adj x p2) : p1 = p2 := by sorry
