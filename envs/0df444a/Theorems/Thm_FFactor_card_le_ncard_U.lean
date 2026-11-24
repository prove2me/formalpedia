-- Prove2me | Theorems.Thm_FFactor_card_le_ncard_U
-- name    : FFactor.card_le_ncard_U
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T06:02:55.989121+00:00
-- url     : https://prove2.me/theorems/620882f7-2a3c-4387-93b8-df11a4b79071
-- title:
--   FFactor: card le ncard U
-- statement:
--   The FFactor construction uses the card le ncard U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L356-L369
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L356-L369

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
omit [DecidableEq V]

theorem FFactor.card_le_ncard_U :
    ∑ v ∈ Sset G f U, G.degree v + ∑ v ∈ Tset G f U, (G.degree v - f v) ≤ U.ncard := by sorry
