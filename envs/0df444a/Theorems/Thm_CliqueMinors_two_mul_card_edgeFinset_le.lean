-- Prove2me | Theorems.Thm_CliqueMinors_two_mul_card_edgeFinset_le
-- name    : CliqueMinors.two_mul_card_edgeFinset_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:41:58.533583+00:00
-- url     : https://prove2.me/theorems/be8cd37a-78a2-4aa1-ba60-9236019c4279
-- title:
--   Clique Minors: two mul card edge Finset le
-- statement:
--   At most `n (n - 1) / 2` edges on a support of `n` vertices.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/MaderFive.lean#L53-L63
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/MaderFive.lean#L53-L63

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]

theorem CliqueMinors.two_mul_card_edgeFinset_le {G : SimpleGraph V} {S : Finset V}
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) :
    2 * G.edgeFinset.card ≤ S.card * (S.card - 1) := by sorry
