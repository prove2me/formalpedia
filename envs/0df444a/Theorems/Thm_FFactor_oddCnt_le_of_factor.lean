-- Prove2me | Theorems.Thm_FFactor_oddCnt_le_of_factor
-- name    : FFactor.oddCnt_le_of_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:53:56.111972+00:00
-- url     : https://prove2.me/theorems/fc944216-bc81-443f-904d-a2ec3e376935
-- title:
--   FFactor: odd Cnt le of factor
-- statement:
--   Necessity in Tutte's f-factor theorem (classical formulation).
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorNec.lean#L246-L251
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorNec.lean#L246-L251

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

theorem FFactor.oddCnt_le_of_factor (G H : SimpleGraph V) (hHG : H ≤ G) (f : V → ℕ)
    (hdeg : ∀ v, #{u | H.Adj v u} = f v) (S T : Finset V) (hST : Disjoint S T) :
    (oddCnt G f S T : ℤ) ≤
      ∑ v ∈ S, (f v : ℤ) - ∑ v ∈ T, (f v : ℤ) + ∑ v ∈ T, (#{u | G.Adj v u ∧ u ∉ S} : ℤ) := by sorry
