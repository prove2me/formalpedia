-- Prove2me | Theorems.Thm_FFactor_sum_split3
-- name    : FFactor.sum_split3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:53:41.894808+00:00
-- url     : https://prove2.me/theorems/1bb6b698-e131-4acd-992e-130f2cdc4976
-- title:
--   FFactor: sum split3
-- statement:
--   Splitting a sum over `V` along the disjoint sets `S`, `T` and `V \ (S ∪ T)`.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorNec.lean#L168-L170
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorNec.lean#L168-L170

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

theorem FFactor.sum_split3 {S T : Finset V} (hST : Disjoint S T) (F : V → ℤ) :
    ∑ u, F u = ∑ u ∈ S, F u + ∑ u ∈ T, F u + ∑ u ∈ univ \ (S ∪ T), F u := by sorry
