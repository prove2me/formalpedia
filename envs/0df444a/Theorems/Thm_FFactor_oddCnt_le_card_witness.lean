-- Prove2me | Theorems.Thm_FFactor_oddCnt_le_card_witness
-- name    : FFactor.oddCnt_le_card_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:53:31.650212+00:00
-- url     : https://prove2.me/theorems/8394e01f-cd2f-481b-98bc-a0eb7904350a
-- title:
--   FFactor: odd Cnt le card witness
-- statement:
--   `q(S, T)` is at most the number of witnesses.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorNec.lean#L127-L165
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorNec.lean#L127-L165

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

theorem FFactor.oddCnt_le_card_witness (G H : SimpleGraph V) (hHG : H ≤ G) (f : V → ℕ)
    (hdeg : ∀ v, #{u | H.Adj v u} = f v) (S T : Finset V) :
    oddCnt G f S T ≤ #{p ∈ (univ \ (S ∪ T)) ×ˢ (univ : Finset V) |
      (p.2 ∈ S ∧ H.Adj p.1 p.2) ∨ (p.2 ∈ T ∧ G.Adj p.1 p.2 ∧ ¬H.Adj p.1 p.2)} := by sorry
