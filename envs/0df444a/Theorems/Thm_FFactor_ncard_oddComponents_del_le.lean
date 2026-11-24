-- Prove2me | Theorems.Thm_FFactor_ncard_oddComponents_del_le
-- name    : FFactor.ncard_oddComponents_del_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:51:42.625006+00:00
-- url     : https://prove2.me/theorems/1cc0fac9-2104-4233-8e6d-6ca8f1b09451
-- title:
--   FFactor: ncard odd Components del le
-- statement:
--   The FFactor construction uses the ncard odd Components del le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorComp.lean#L104-L215
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorComp.lean#L104-L215

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {W : Type*} (Γ : SimpleGraph W)

theorem FFactor.ncard_oddComponents_del_le [Finite W] (U : Set W) (x : W) (hx : x ∈ U)
    (h3 : ∀ a b c : ((⊤ : Γ.Subgraph).deleteVerts U).verts, Γ.Adj x a → Γ.Adj x b →
      Γ.Adj x c → (del Γ U).Reachable a b ∨ (del Γ U).Reachable a c ∨
        (del Γ U).Reachable b c) :
    (del Γ U).oddComponents.ncard ≤ (del Γ (U \ {x})).oddComponents.ncard + 1 := by sorry
