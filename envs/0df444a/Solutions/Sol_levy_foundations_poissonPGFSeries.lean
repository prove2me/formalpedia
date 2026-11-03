-- Prove2me | solution 1 for levy_foundations_poissonPGFSeries
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:34:19.093303+00:00
-- url     : https://prove2.me/submissions/a89d4a97-8777-4af1-a189-677573239bc6

import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal

theorem solution
    (lam : ℝ≥0) (w : ℂ) :
    ∑' j : ℕ, ((poissonMeasure lam).real {j} : ℂ) * w ^ j =
      Complex.exp ((lam : ℝ) * (w - 1)) := by
  have hterm : ∀ j : ℕ,
      ((poissonMeasure lam).real {j} : ℂ) * w ^ j =
        (Real.exp (-(lam : ℝ)) : ℂ) *
          (((lam : ℝ) * w) ^ j / (Nat.factorial j : ℂ)) := by
    intro j
    simp only [poissonMeasure_real_singleton]
    push_cast
    rw [mul_pow]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hsum := NormedSpace.expSeries_div_hasSum_exp (((lam : ℝ) : ℂ) * w)
  rw [hsum.tsum_eq, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring
