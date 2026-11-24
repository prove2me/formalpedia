-- Prove2me | Theorems.Thm_FFactor_card_fiber_TT
-- name    : FFactor.card_fiber_TT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T06:01:53.944288+00:00
-- url     : https://prove2.me/theorems/d49130c3-8c50-41f3-b135-7295fd835203
-- title:
--   FFactor: card fiber TT
-- statement:
--   The FFactor construction uses the card fiber TT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L183-L214
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L183-L214

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

theorem FFactor.card_fiber_TT (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {d : G.Dart}
    (hd : (.inl d : GV G f) ∉ U) (h1 : d.fst ∈ Tset G f U) (h2 : d.snd ∈ Tset G f U) :
    #{x : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts |
      lab G f U x.1 = .inr (.inl d.edge)} = 2 := by sorry
