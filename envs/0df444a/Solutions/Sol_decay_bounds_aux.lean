-- Prove2me | solution 1 for decay_bounds_aux
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:29:29.534196+00:00
-- url     : https://prove2.me/submissions/092addd3-4685-4ff2-81e2-836d4becf3bb

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

set_option autoImplicit true
open Real MeasureTheory Filter

variable {A : ℝ}

theorem solution {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (h : ∀ t, ‖f t‖ ≤ A * (1 + t ^ 2)⁻¹) :
    ∫ t, ‖f t‖ ≤ π * A := by
  have l1 : Integrable (fun x ↦ A * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul A
  simp_rw [← integral_univ_inv_one_add_sq, mul_comm, ← integral_const_mul]
  exact integral_mono (l1.mono' hf (Eventually.of_forall h)).norm l1 h
