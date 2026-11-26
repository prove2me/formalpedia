-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_clique_side
-- name    : BrooksTheorem.Aux.clique_side
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:32:46.343074+00:00
-- url     : https://prove2.me/theorems/be51f14c-d42e-56c0-bd87-15c87b1d76e1
-- title:
--   Aux: clique side
-- statement:
--   The Aux construction uses the clique side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L248-L355
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L248-L355

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

theorem BrooksTheorem.Aux.clique_side {k : ℕ} (hk : 3 ≤ k) {H : SimpleGraph V} (ih : IHyp k H)
    (hdeg : ∀ v, (nb H v).card ≤ k) (hcf : H.CliqueFree (k + 1)) (S : Set V) {x z px pz : V}
    (hxz : x ≠ z) (hn : ¬ H.Adj x z) (hpx : H.Adj x px) (hpxS : px ∉ S)
    (hpz : H.Adj z pz) (hpzS : pz ∉ S)
    (hK : ¬ (restr H S ⊔ edge x z).CliqueFree (k + 1)) :
    (∃ c : V → Fin k, Proper (restr H S) c ∧ c x = c z) ∧
    (∀ v ∉ S, H.Adj x v → v = px) ∧ (∀ v ∉ S, H.Adj z v → v = pz) := by sorry
