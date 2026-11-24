-- Prove2me | Theorems.Thm_FFactor_mem_del_verts
-- name    : FFactor.mem_del_verts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:51:24.350788+00:00
-- url     : https://prove2.me/theorems/9c6de8b1-8f93-45d2-9701-f54360d96e05
-- title:
--   FFactor: mem del verts
-- statement:
--   The FFactor construction uses the mem del verts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorComp.lean#L85-L86
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorComp.lean#L85-L86

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {W : Type*} (Γ : SimpleGraph W)

theorem FFactor.mem_del_verts {U : Set W} {a : W} :
    a ∈ ((⊤ : Γ.Subgraph).deleteVerts U).verts ↔ a ∉ U := by sorry
