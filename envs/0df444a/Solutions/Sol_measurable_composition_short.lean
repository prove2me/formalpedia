-- Prove2me | solution 1 for measurable_composition_short
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:12.709432+00:00
-- url     : https://prove2.me/submissions/1770a202-f95d-46bb-8bb6-549053b4a5ae

import Mathlib.MeasureTheory.MeasurableSpace.Basic
section Theorem_4_3
variable {Ω Ω' Ω'' : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']

theorem solution {f : Ω → Ω'} {g : Ω' → Ω''}
    (hf : Measurable f) (hg : Measurable g) : Measurable (g ∘ f) := by
  exact hg.comp hf
end Theorem_4_3

