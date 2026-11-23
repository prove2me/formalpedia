-- Prove2me | solution 1 for inf_occ_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:19:06.102933+00:00
-- url     : https://prove2.me/submissions/24e33b21-bf72-46df-bf68-877c7f15eeb5

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc

set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'
theorem _root_.solution {X : Type*} [Finite X] (xs : Stream' X) :
    ∀ᶠ k in atTop, xs k ∈ InfOcc xs := by
  have h_compl : ∀ x ∈ (InfOcc xs)ᶜ, ∃ n, ∀ k ≥ n, xs k ≠ x := by simp [InfOcc]
  choose lb h_lb using h_compl
  let fs_compl := Finite.toFinset <| toFinite (InfOcc xs)ᶜ
  let glb := fs_compl.sup (fun x ↦ if h : x ∈ (InfOcc xs)ᶜ then lb x h else 0)
  have h_glb : ∀ x, (h : x ∈ (InfOcc xs)ᶜ) → lb x h ≤ glb := by
    intro x h ; refine Finset.le_sup_of_le (b := x) (by simpa [fs_compl]) (by simp [h])
  apply eventually_atTop.mpr
  use glb ; intro k h_k ; by_contra h_contra
  have := h_glb (xs k) h_contra
  have := h_lb (xs k) h_contra k (by omega)
  contradiction
