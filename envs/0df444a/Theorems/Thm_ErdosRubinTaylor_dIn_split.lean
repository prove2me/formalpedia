-- Prove2me | Theorems.Thm_ErdosRubinTaylor_dIn_split
-- name    : ErdosRubinTaylor.dIn_split
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:31:26.116316+00:00
-- url     : https://prove2.me/theorems/545adc1f-78df-5028-9b5f-c67ff22ab8c6
-- title:
--   Erdos Rubin Taylor: d In split
-- statement:
--   The Erdos Rubin Taylor construction uses the d In split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L137-L190
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L137-L190

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_ChoosabilityLib_ERTGallai
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V]

theorem ErdosRubinTaylor.dIn_split {T A B : Set V} {x : V} (hAB : A ∪ B = T \ {x}) (hdisj : Disjoint A B)
    (hx : x ∈ T) (hnoadj : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    (∀ v ∈ A, dIn G T v = dIn G (insert x A) v) ∧
    (∀ v ∈ B, dIn G T v = dIn G (insert x B) v) ∧
    dIn G T x = dIn G (insert x A) x + dIn G (insert x B) x := by sorry
