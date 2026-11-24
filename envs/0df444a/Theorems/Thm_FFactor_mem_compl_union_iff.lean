-- Prove2me | Theorems.Thm_FFactor_mem_compl_union_iff
-- name    : FFactor.mem_compl_union_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:53:28.304796+00:00
-- url     : https://prove2.me/theorems/ca06cc97-34fa-49ff-9590-b2e43075d2c1
-- title:
--   FFactor: mem compl union iff
-- statement:
--   Membership in the complement of `S ∪ T`.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorNec.lean#L53-L55
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorNec.lean#L53-L55

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorNec
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]

theorem FFactor.mem_compl_union_iff {S T : Finset V} {u : V} :
    u ∈ ((S ∪ T : Finset V) : Set V)ᶜ ↔ u ∉ S ∧ u ∉ T := by sorry
