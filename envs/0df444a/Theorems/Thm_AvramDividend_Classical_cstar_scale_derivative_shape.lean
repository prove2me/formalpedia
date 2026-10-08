-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_scale_derivative_shape
-- name    : AvramDividend.Classical.cstar_scale_derivative_shape
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T21:54:18.214729+00:00
-- url     : https://prove2.me/theorems/b883f1c9-6b75-48a3-b3d3-983b596474b6
-- title:
--   Analytic scale-function shape at the finite optimal barrier
-- statement:
--   For a spectrally negative Lévy process satisfying the standing assumptions and its q-scale function W (q>0), suppose the canonical barrier c* is finite. Either c*=0 and W(0)=0, or there is a strictly positive reference derivative d at c* such that the extended-real denominator at c* equals d, each nonnegative competing barrier has an infinite, zero, or at least d effective denominator, and the secant slope of W on every subinterval of [0,c*] is at least d. The second alternative includes the finite positive boundary derivative at zero when W(0)>0. This is the analytic input for the already-proved conditional Proposition 3(i) comparison, and requires smoothness, derivative-minimum closure, positivity, and one-sided boundary analysis.
-- source:
--   Avram, Palmowski and Pistorius, On the optimal dividend problem for a spectrally negative Lévy process I, arXiv:math/0702893v1, p. 5 (3.3)-(3.4), p. 13 (5.1)-(5.2), p. 15 Proposition 3(i). This isolates the scale-function analysis from the proved algebraic comparison cstar_optimal_barrier_of_shape.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Scale-function shape package needed for Proposition 3(i).
The zero-barrier alternative handles zero initial scale value.
The other branch supplies a positive denominator, global denominator
comparison, and the secant inequality below the canonical barrier. -/
theorem AvramDividend.Classical.cstar_scale_derivative_shape
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hfinite : cstar W < ⊤) :
    ((cstar W).toReal = 0 ∧ W 0 = 0) ∨
      ∃ d : ℝ, 0 < d ∧
        scaleDeriv W (cstar W).toReal = (d : EReal) ∧
        (∀ a : ℝ, 0 ≤ a →
          scaleDeriv W a = ⊤ ∨
            (scaleDeriv W a).toReal = 0 ∨
            d ≤ (scaleDeriv W a).toReal) ∧
        (∀ b x : ℝ, 0 ≤ b → b ≤ x →
          x ≤ (cstar W).toReal →
          (x - b) * d ≤ W x - W b) := by sorry
