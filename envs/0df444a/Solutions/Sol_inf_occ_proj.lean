-- Prove2me | solution 1 for inf_occ_proj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:35:18.985827+00:00
-- url     : https://prove2.me/submissions/aec08d4d-29e2-4b1f-a308-ec4247597853

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Theorems.Thm_frequently_iff_strict_mono
import Theorems.Thm_frequently_in_finite_set

set_option autoImplicit true
open Function Set Prod Option Filter Stream'
open Classical
attribute [local instance_reducible] Stream'
theorem _root_.solution {I : Type*} [Finite I] {X : I → Type*} [h : ∀ i, Finite (X i)] (xs : Stream' (Π i, X i)) (i : I) :
    (· i) '' (InfOcc xs) = InfOcc ((· i) ∘ xs) := by
  ext x_i ; simp ; constructor
  · rintro ⟨x, h_inf, rfl⟩
    obtain ⟨φ, h_mono, h_x⟩ := frequently_iff_strict_mono.mp h_inf
    apply frequently_iff_strict_mono.mpr
    exact ⟨φ, h_mono, fun m => congrArg (fun x => x i) (h_x m)⟩
  · intro h_inf
    let s := { x : Π i, X i | x i = x_i }
    have h_inf' : ∃ᶠ k in atTop, xs k ∈ s := by exact h_inf
    obtain ⟨x, h_x, h_inf''⟩ := frequently_in_finite_set.mp h_inf'
    aesop
