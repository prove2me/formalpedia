-- Prove2me | Theorems.Thm_FFactor_exists_factor_of_matching
-- name    : FFactor.exists_factor_of_matching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:52:22.255916+00:00
-- url     : https://prove2.me/theorems/e50c7a97-7d0c-4af2-9f4c-82c273c9875e
-- title:
--   FFactor: exists factor of matching
-- statement:
--   A perfect matching of the gadget gives an f-factor of `G`.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorGadget.lean#L62-L135
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorGadget.lean#L62-L135

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorGadget
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] (G : SimpleGraph V) (f : V → ℕ)
variable {G f}

theorem FFactor.exists_factor_of_matching (hf : ∀ v, f v ≤ G.degree v) (M : (gadget G f).Subgraph)
    (hM : M.IsPerfectMatching) :
    ∃ H : SimpleGraph V, H ≤ G ∧ ∀ v, #{u | H.Adj v u} = f v := by sorry
