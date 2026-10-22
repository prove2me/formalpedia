-- Prove2me | solution 1 for eq30_hasDerivWithinAt_sub_const
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:16:55.118272+00:00
-- url     : https://prove2.me/submissions/be57ba99-056f-4314-bf02-f35ee89fbb5f

import Mathlib
set_option autoImplicit false

theorem solution
    (g : ℝ → ℝ) (s x d : ℝ)
    (hg : HasDerivWithinAt g d (Set.Ici (s - x)) (s - x)) :
    HasDerivWithinAt (fun t => g (t - x)) d (Set.Ici s) s := by
  have h1 : HasDerivWithinAt (fun t : ℝ => t - x) 1 (Set.Ici s) s :=
    (hasDerivWithinAt_id s _).sub_const x
  have h2 : Set.MapsTo (fun t : ℝ => t - x) (Set.Ici s) (Set.Ici (s - x)) := by
    intro t ht
    simp only [Set.mem_Ici] at ht ⊢
    linarith
  have := hg.scomp s h1 h2
  rw [one_smul] at this
  exact this
