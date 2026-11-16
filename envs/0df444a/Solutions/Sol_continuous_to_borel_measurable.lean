-- Prove2me | solution 1 for continuous_to_borel_measurable
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:09.782358+00:00
-- url     : https://prove2.me/submissions/4d6c11f8-10c0-488b-a0f3-cd198062f40c

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
section Theorem_4_5
open MeasureTheory

theorem solution {m n : ℕ} (f : (Fin m → ℝ) → (Fin n → ℝ))
    (hf : Continuous f) : Measurable f := by
  exact hf.measurable
end Theorem_4_5

