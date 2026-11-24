-- Prove2me | Theorems.Thm_FFactor_oddComponents_ncard_eq_of_label
-- name    : FFactor.oddComponents_ncard_eq_of_label
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:51:37.642889+00:00
-- url     : https://prove2.me/theorems/fc8bc185-123b-4819-a9b1-fb01bb5d5f0d
-- title:
--   FFactor: odd Components ncard eq of label
-- statement:
--   The FFactor construction uses the odd Components ncard eq of label property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorComp.lean#L38-L73
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorComp.lean#L38-L73

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {X L : Type*} (H : SimpleGraph X) (φ : X → L)
open Classical

theorem FFactor.oddComponents_ncard_eq_of_label [Fintype X]
    (h1 : ∀ x y, H.Adj x y → φ x = φ y) (h2 : ∀ x y, φ x = φ y → H.Reachable x y) :
    H.oddComponents.ncard = #{l ∈ univ.image φ | Odd #{x | φ x = l}} := by sorry
