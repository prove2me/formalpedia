-- Prove2me | Theorems.Thm_FFactor_exists_factor_of_condition
-- name    : FFactor.exists_factor_of_condition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T06:02:50.294924+00:00
-- url     : https://prove2.me/theorems/ee0995f9-97a6-48a5-80a9-58288875b2e8
-- title:
--   FFactor: exists factor of condition
-- statement:
--   Sufficiency in Tutte's f-factor theorem (classical formulation).
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L378-L426
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L378-L426

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
variable (G f)

theorem FFactor.exists_factor_of_condition
    (h : ∀ S T : Finset V, Disjoint S T → (oddCnt G f S T : ℤ) ≤
      ∑ v ∈ S, (f v : ℤ) - ∑ v ∈ T, (f v : ℤ) + ∑ v ∈ T, (#{u | G.Adj v u ∧ u ∉ S} : ℤ)) :
    ∃ H : SimpleGraph V, H ≤ G ∧ ∀ v, #{u | H.Adj v u} = f v := by sorry
