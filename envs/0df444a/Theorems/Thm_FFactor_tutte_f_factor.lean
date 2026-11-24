-- Prove2me | Theorems.Thm_FFactor_tutte_f_factor
-- name    : FFactor.tutte_f_factor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:58:54.860766+00:00
-- url     : https://prove2.me/theorems/ad28147d-2dca-44a5-8139-3fcf1b66ba29
-- title:
--   FFactor: tutte f factor
-- statement:
--   **Tutte's f-factor theorem.** A finite simple graph `G` has a spanning subgraph `H` with
--   `deg_H v = f v` for every vertex `v` if and only if, for all disjoint vertex sets `S` and `T`,
--   `q(S, T) ≤ ∑_{v ∈ S} f v − ∑_{v ∈ T} f v + ∑_{v ∈ T} deg_{G − S} v`.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactor.lean#L48-L78
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactor.lean#L48-L78

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorNec
public import Definitions.Def_FFactorLib_FFactorCount
public import Definitions.Def_FFactorLib_FFactor
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem FFactor.tutte_f_factor (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℕ) :
    (∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj, H ≤ G ∧ ∀ v, H.degree v = f v) ↔
      ∀ S T : Finset V, Disjoint S T →
        (oddCount G f S T : ℤ) ≤ ∑ v ∈ S, (f v : ℤ) - ∑ v ∈ T, (f v : ℤ) +
          ∑ v ∈ T, (#{u ∈ G.neighborFinset v | u ∉ S} : ℤ) := by sorry
