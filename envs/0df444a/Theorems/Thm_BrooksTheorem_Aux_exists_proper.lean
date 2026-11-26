-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_exists_proper
-- name    : BrooksTheorem.Aux.exists_proper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:33:28.625383+00:00
-- url     : https://prove2.me/theorems/bba63cb2-288e-4fd1-8e19-2ccd301b2abc
-- title:
--   Aux: exists proper
-- statement:
--   The core statement: every graph on `V` with all degrees at most `k ≥ 3` and no
--   `(k + 1)`-clique has a proper `k`-colouring.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L573-L582
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L573-L582

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

theorem BrooksTheorem.Aux.exists_proper (k : ℕ) (hk : 3 ≤ k) (H : SimpleGraph V)
    (hdeg : ∀ v, (nb H v).card ≤ k) (hcf : H.CliqueFree (k + 1)) :
    ∃ f : V → Fin k, Proper H f := by sorry
