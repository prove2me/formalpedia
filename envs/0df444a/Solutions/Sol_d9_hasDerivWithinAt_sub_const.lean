-- Prove2me | solution 1 for d9_hasDerivWithinAt_sub_const
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T04:59:39.829716+00:00
-- url     : https://prove2.me/submissions/52a9b6a0-ed01-44be-a152-6dbf53523fc5

import Mathlib

theorem solution (g : ℝ → ℝ) (s x d : ℝ)
    (hg : HasDerivWithinAt g d (Set.Ici (s - x)) (s - x)) :
    HasDerivWithinAt (fun t => g (t - x)) d (Set.Ici s) s := by
  have hmap : Set.MapsTo (fun t : ℝ => t - x) (Set.Ici s) (Set.Ici (s - x)) := by
    intro t ht
    simp only [Set.mem_Ici] at ht ⊢
    linarith
  have hlin : HasDerivWithinAt (fun t : ℝ => t - x) (1 : ℝ) (Set.Ici s) s := by
    simpa using ((hasDerivAt_id' (s : ℝ)).hasDerivWithinAt (s := Set.Ici s)).sub_const x
  -- Match the NormedAlgebra instances produced by `HasDerivWithinAt.comp`.
  change HasDerivWithinAt (g ∘ fun t : ℝ => t - x) d (Set.Ici s) s
  simpa using hg.comp s hlin hmap
