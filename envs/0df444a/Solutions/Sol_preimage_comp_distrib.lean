-- Prove2me | solution 1 for preimage_comp_distrib
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:14.001672+00:00
-- url     : https://prove2.me/submissions/a93b7e4c-8128-43cb-a82e-8925d49934fc

import Mathlib.Data.Set.Lattice
open Set
universe u v w
variable {Ω : Type u} {Ω' : Type v} {Ω'' : Type w} {I : Type _}
variable (f : Ω → Ω') (g : Ω' → Ω'') (A : Set Ω') (Ai : I → Set Ω') (B : Set Ω'')

theorem solution (h : Ω → Ω'') (hw : h = g ∘ f) :
    h ⁻¹' B = f ⁻¹' (g ⁻¹' B) := by
  subst hw
  rfl

