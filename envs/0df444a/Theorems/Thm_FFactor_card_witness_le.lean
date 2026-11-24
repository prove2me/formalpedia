-- Prove2me | Theorems.Thm_FFactor_card_witness_le
-- name    : FFactor.card_witness_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:53:53.675742+00:00
-- url     : https://prove2.me/theorems/15c14ecd-5c39-4ab1-9280-93a3a178e79d
-- title:
--   FFactor: card witness le
-- statement:
--   The number of witnesses is bounded by the right-hand side of the f-factor condition.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorNec.lean#L174-L242
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorNec.lean#L174-L242

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

theorem FFactor.card_witness_le (G H : SimpleGraph V) (hHG : H ≤ G) (f : V → ℕ)
    (hdeg : ∀ v, #{u | H.Adj v u} = f v) (S T : Finset V) (hST : Disjoint S T) :
    (#{p ∈ (univ \ (S ∪ T)) ×ˢ (univ : Finset V) |
      (p.2 ∈ S ∧ H.Adj p.1 p.2) ∨ (p.2 ∈ T ∧ G.Adj p.1 p.2 ∧ ¬H.Adj p.1 p.2)} : ℤ) ≤
      ∑ v ∈ S, (f v : ℤ) - ∑ v ∈ T, (f v : ℤ) + ∑ v ∈ T, (#{u | G.Adj v u ∧ u ∉ S} : ℤ) := by sorry
