-- Prove2me | Theorems.Thm_CliqueMinors_contract_support
-- name    : CliqueMinors.contract_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:33:21.621237+00:00
-- url     : https://prove2.me/theorems/79f989c7-d53c-507e-a8da-d54012484c79
-- title:
--   Clique Minors: contract support
-- statement:
--   The Clique Minors construction uses the contract support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L115-L123
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/GraphOps.lean#L115-L123

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]
omit [Fintype V]

theorem CliqueMinors.contract_support {G : SimpleGraph V} {S : Finset V} {x y : V} (hxy : G.Adj x y)
    (hsupp : ∀ a b, G.Adj a b → a ∈ S) :
    ∀ a b, (contractG G x y).Adj a b → a ∈ S.erase y := by sorry
