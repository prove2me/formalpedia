-- Prove2me | Theorems.Thm_FFactor_ncard_odd_le
-- name    : FFactor.ncard_odd_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T06:02:22.584601+00:00
-- url     : https://prove2.me/theorems/aed55a6e-06df-46c4-8826-2db7220cc925
-- title:
--   FFactor: ncard odd le
-- statement:
--   The FFactor construction uses the ncard odd le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L216-L298
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L216-L298

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

theorem FFactor.ncard_odd_le (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x)
    (hf : ∀ v, f v ≤ G.degree v) :
    (del (gadget G f) U).oddComponents.ncard ≤ oddCnt G f (Sset G f U) (Tset G f U) +
      #{d : G.Dart | d.fst ∈ Tset G f U ∧ d.snd ∈ Sset G f U} +
      #{p : Σ v : V, Fin (G.degree v - f v) | p.1 ∈ Sset G f U} := by sorry
