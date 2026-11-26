-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_step
-- name    : BrooksTheorem.Aux.step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:33:34.304925+00:00
-- url     : https://prove2.me/theorems/c5d22494-222a-5ed0-9bc0-241aa9f52534
-- title:
--   Aux: step
-- statement:
--   The Aux construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L397-L569
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L397-L569

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

theorem BrooksTheorem.Aux.step {k : ℕ} (hk : 3 ≤ k) {H : SimpleGraph V} (ih : IHyp k H)
    (hdeg : ∀ v, (nb H v).card ≤ k) (hcf : H.CliqueFree (k + 1)) :
    ∃ f : V → Fin k, Proper H f := by sorry
