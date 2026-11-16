-- Prove2me | solution 1 for preimage_iUnion_distrib
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:14.749021+00:00
-- url     : https://prove2.me/submissions/9c136a5c-a598-4646-af7c-06ee5559f8ac

import Mathlib.Data.Set.Lattice
open Set
universe u v w
variable {Ω : Type u} {Ω' : Type v} {Ω'' : Type w} {I : Type _}
variable (f : Ω → Ω') (g : Ω' → Ω'') (A : Set Ω') (Ai : I → Set Ω') (B : Set Ω'')

theorem solution : f ⁻¹' (⋃ i, Ai i) = ⋃ i, f ⁻¹' (Ai i) := by
  ext x
  simp

