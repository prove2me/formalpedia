-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_few_side
-- name    : BrooksTheorem.Aux.few_side
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:56.7462+00:00
-- url     : https://prove2.me/theorems/2fd72be9-9756-4946-a069-a2cb1858bf62
-- title:
--   Aux: few side
-- statement:
--   The Aux construction uses the few side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L357-L373
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L357-L373

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
variable [Fintype V]

theorem BrooksTheorem.Aux.few_side {k : ℕ} (hk : 3 ≤ k) {H : SimpleGraph V} (ih : IHyp k H)
    (hdeg : ∀ v, (nb H v).card ≤ k) (hcf : H.CliqueFree (k + 1)) (S : Set V) {x z qx qz w : V}
    (hn : ¬ H.Adj x z) (hw : H.Adj x w)
    (hx1 : ∀ v ∈ S, v ≠ z → H.Adj x v → v = qx) (hz1 : ∀ v ∈ S, v ≠ x → H.Adj z v → v = qz) :
    ∃ c : V → Fin k, Proper (restr H S) c ∧ c x = c z := by sorry
