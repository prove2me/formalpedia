-- Prove2me | Theorems.Thm_FFactor_reach_inner_of_reachable
-- name    : FFactor.reach_inner_of_reachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T06:01:02.781963+00:00
-- url     : https://prove2.me/theorems/ca10c8ad-f1d2-4612-a5a0-20586173f940
-- title:
--   FFactor: reach inner of reachable
-- statement:
--   The FFactor construction uses the reach inner of reachable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L305-L318
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L305-L318

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
public import Theorems.Thm_FFactor_mem_del_verts
attribute [local simp] FFactor.mem_del_verts


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}
variable [DecidableEq V] {U : Set (GV G f)}

theorem FFactor.reach_inner_of_reachable (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x)
    {u w : ↥(((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ)} (p : (Gr G f U).Walk u w) :
    ∀ (i : Fin (G.degree u.1 - f u.1)) (i' : Fin (G.degree w.1 - f w.1)),
    (del (gadget G f) U).Reachable
      ⟨.inr ⟨u.1, i⟩, (mem_del_verts _).mpr (F1 hmin (notMem_T_of_notMem_union u.2) i)⟩
      ⟨.inr ⟨w.1, i'⟩, (mem_del_verts _).mpr (F1 hmin (notMem_T_of_notMem_union w.2) i')⟩ := by sorry
