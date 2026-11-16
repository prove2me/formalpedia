-- Prove2me | solution 1 for continuous_preimage_borel
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:23:09.221025+00:00
-- url     : https://prove2.me/submissions/45426bb8-fa08-49fa-a88c-e6580950e855

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
section Theorem_4_5
open MeasureTheory

theorem solution {m n : ℕ} (f : (Fin m → ℝ) → (Fin n → ℝ))
    (hf : Continuous f) (B : Set (Fin n → ℝ)) (hB : MeasurableSet B) :
    MeasurableSet (f ⁻¹' B) := by
  exact hf.measurable hB
end Theorem_4_5

