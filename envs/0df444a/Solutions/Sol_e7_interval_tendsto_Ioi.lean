-- Prove2me | solution 1 for e7_interval_tendsto_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T07:15:35.149765+00:00
-- url     : https://prove2.me/submissions/b9218a99-653a-4ab4-abc3-3348e5e5f6d8

import Mathlib

open MeasureTheory Set Filter

theorem solution (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioi 0) volume) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t) atTop
      (nhds (∫ t, f t ∂(volume.restrict (Set.Ioi 0)))) :=
  intervalIntegral_tendsto_integral_Ioi 0 hf tendsto_id
