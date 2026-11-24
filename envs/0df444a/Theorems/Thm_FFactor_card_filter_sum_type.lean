-- Prove2me | Theorems.Thm_FFactor_card_filter_sum_type
-- name    : FFactor.card_filter_sum_type
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T06:01:08.253538+00:00
-- url     : https://prove2.me/theorems/c2c52da0-fc43-4eca-9cb7-0c9b23853bfc
-- title:
--   FFactor: card filter sum type
-- statement:
--   Cardinality of a filter over a sum type.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L32-L35
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L32-L35

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorSuff
public import Definitions.Def_FFactorLib_FFactorCount
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {f : V → ℕ}
  {U : Set (GV G f)}

theorem FFactor.card_filter_sum_type {α β : Type*} [Fintype α] [Fintype β] (P : α ⊕ β → Prop)
    [DecidablePred P] :
    #{x | P x} = #{a | P (.inl a)} + #{b | P (.inr b)} := by sorry
