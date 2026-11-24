-- Prove2me | Theorems.Thm_FFactor_odd_fiber_iff
-- name    : FFactor.odd_fiber_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T06:01:50.788732+00:00
-- url     : https://prove2.me/theorems/b2de3a18-7a32-49c3-8af0-6ee9b25e7f0b
-- title:
--   FFactor: odd fiber iff
-- statement:
--   The FFactor construction uses the odd fiber iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L122-L181
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L122-L181

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

theorem FFactor.odd_fiber_iff (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x)
    (hf : ∀ v, f v ≤ G.degree v) (c : (Gr G f U).ConnectedComponent) :
    Odd #{x : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts | lab G f U x.1 = .inl c} ↔
    Odd (∑ w ∈ univ.filter (fun w : ↥(((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ) =>
        (G.induce ((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ).connectedComponentMk w = c),
      (f w + #{t ∈ Tset G f U | G.Adj w t})) := by sorry
