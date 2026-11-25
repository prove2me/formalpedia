-- Prove2me | Theorems.Thm_ErdosPosa_edges_restr
-- name    : ErdosPosa.edges_restr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:30:29.939942+00:00
-- url     : https://prove2.me/theorems/bd51a808-b0be-4960-9bd2-e945cb97f4f4
-- title:
--   Erdos Posa: edges restr
-- statement:
--   The Erdos Posa construction uses the edges restr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPin.lean#L67-L71
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPin.lean#L67-L71

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMaximal
public import Definitions.Def_ErdosPosaLib_EPPin
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.edges_restr {G : SimpleGraph V} {X : Set V} {a b : V} (p : (restr G X).Walk a b)
    {e : Sym2 V} (he : e ∈ p.edges) : ∃ c d, e = s(c, d) ∧ c ≠ d ∧ c ∈ X ∧ d ∈ X := by sorry
