-- Prove2me | Theorems.Thm_FFactor_card_filter_verts
-- name    : FFactor.card_filter_verts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:58:22.957949+00:00
-- url     : https://prove2.me/theorems/660bd3f3-c64c-4a4e-9dce-f17fbf19025c
-- title:
--   FFactor: card filter verts
-- statement:
--   Cardinality of a filter over the vertices of `gadget - U`.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L39-L49
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L39-L49

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
omit [DecidableEq V]

theorem FFactor.card_filter_verts (P : GV G f → Prop) [DecidablePred P]
    [DecidablePred (fun x : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts => P x.1)] :
    #{x : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts | P x.1} = #{a | a ∉ U ∧ P a} := by sorry
