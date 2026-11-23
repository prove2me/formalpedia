-- Prove2me | solution 1 for inf_occ_opt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:53:44.698718+00:00
-- url     : https://prove2.me/submissions/55865abf-2657-4cf2-9242-edff743bc54a

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Theorems.Thm_inf_occ_suffix
import Theorems.Thm_inf_occ_eventually
import Theorems.Thm_P2M_Stream__get_drop__05b839498f63


set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'
theorem _root_.solution {X : Type*} [Finite X] (os : Stream' (Option X)) (y : X)
    (h : ∀ o ∈ InfOcc os, o.isSome) :
    {x | ∃ o ∈ InfOcc os, o = some x} = InfOcc ((getD · y) ∘ os) := by
  ext x ; constructor
  · rintro ⟨o, h_inf, rfl⟩
    apply Frequently.mono h_inf
    intro k h_k ; simp [h_k]
  · intro h_inf ; simp
    obtain ⟨n, h_n⟩ := eventually_atTop.mp <| inf_occ_eventually os
    have h_n' : ∀ m ≥ n, ∃ x, os m = some x := by
      intro m h_m
      exact isSome_iff_exists.mp <| h (os m) <| h_n m h_m
    simp [← inf_occ_suffix os n]
    simp [← inf_occ_suffix ((getD · y) ∘ os) n] at h_inf
    apply Frequently.mono h_inf
    intro k
    obtain ⟨x', h_x'⟩ := h_n' (n + k) (by omega)
    simp [get_drop', h_x']
