-- Prove2me | solution 1 for preimage_compl_distrib
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:15.945379+00:00
-- url     : https://prove2.me/submissions/24e3ff04-05f1-4bbb-a8ea-c6928a76bd84

import Mathlib.Data.Set.Lattice
open Set
universe u v w
variable {Ω : Type u} {Ω' : Type v} {Ω'' : Type w} {I : Type _}
variable (f : Ω → Ω') (g : Ω' → Ω'') (A : Set Ω') (Ai : I → Set Ω') (B : Set Ω'')

theorem solution : f ⁻¹' (Aᶜ) = (f ⁻¹' A)ᶜ := by
  rfl

