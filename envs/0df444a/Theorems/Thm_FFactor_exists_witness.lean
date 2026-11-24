-- Prove2me | Theorems.Thm_FFactor_exists_witness
-- name    : FFactor.exists_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:53:28.937635+00:00
-- url     : https://prove2.me/theorems/e13dfefc-3627-44d1-82e6-93bac174d847
-- title:
--   FFactor: exists witness
-- statement:
--   Every component counted by `q(S, T)` has a witness vertex: an `H`-edge to `S` or a
--   `G`-edge to `T` which is not in `H`.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorNec.lean#L60-L123
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorNec.lean#L60-L123

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
open Classical

theorem FFactor.exists_witness (G H : SimpleGraph V) (hHG : H ≤ G) (f : V → ℕ)
    (hdeg : ∀ v, #{u | H.Adj v u} = f v) (S T : Finset V)
    (c : (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).ConnectedComponent)
    (hc : Odd (∑ w ∈ univ.filter (fun w : ↥(((S ∪ T : Finset V) : Set V)ᶜ) =>
        (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).connectedComponentMk w = c),
      (f w + #{t ∈ T | G.Adj w t}))) :
    ∃ w : ↥(((S ∪ T : Finset V) : Set V)ᶜ),
      (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).connectedComponentMk w = c ∧
      ((∃ z ∈ S, H.Adj w z) ∨ (∃ t ∈ T, G.Adj w t ∧ ¬H.Adj w t)) := by sorry
