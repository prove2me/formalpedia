-- Prove2me | solution 1 for preimage_iInter_distrib
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:15.317864+00:00
-- url     : https://prove2.me/submissions/abeea4cb-a28b-4714-9b7b-2af86c4151e7

import Mathlib.Data.Set.Lattice
open Set
universe u v w
variable {Ω : Type u} {Ω' : Type v} {Ω'' : Type w} {I : Type _}
variable (f : Ω → Ω') (g : Ω' → Ω'') (A : Set Ω') (Ai : I → Set Ω') (B : Set Ω'')

theorem solution : f ⁻¹' (⋂ i, Ai i) = ⋂ i, f ⁻¹' (Ai i) := by
  ext x
  simp

