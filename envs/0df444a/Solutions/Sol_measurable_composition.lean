-- Prove2me | solution 1 for measurable_composition
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:13.317204+00:00
-- url     : https://prove2.me/submissions/22d5aef2-8405-48b7-b23f-e1ae054b3324

import Mathlib.MeasureTheory.MeasurableSpace.Basic
section Theorem_4_3
variable {Ω Ω' Ω'' : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']

theorem solution {f : Ω → Ω'} {g : Ω' → Ω''}
    (hf : Measurable f) (hg : Measurable g)
      : Measurable (g ∘ f) := by
  exact hg.comp hf
end Theorem_4_3

