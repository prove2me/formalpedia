-- Prove2me | solution 1 for thm_4_6
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:16.559426+00:00
-- url     : https://prove2.me/submissions/72a1f97e-a7f1-4e4b-a1fb-0a99ff0b3c64

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.MeasurableSpace.Defs


theorem solution {Ω : Type _} [MeasurableSpace Ω] (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (f + g) ∧ Measurable (f - g) ∧ (∀ c : ℝ, Measurable (c • f)) ∧ ((∀ ω, g ω ≠ 0) → Measurable (f / g)) := by
  refine ⟨hf.add hg, hf.sub hg, fun c => hf.const_smul c, fun _ => hf.div hg⟩

