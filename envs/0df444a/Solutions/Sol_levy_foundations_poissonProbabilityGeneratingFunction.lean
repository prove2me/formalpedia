-- Prove2me | solution 1 for levy_foundations_poissonProbabilityGeneratingFunction
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T00:28:01.532119+00:00
-- url     : https://prove2.me/submissions/5e43b87e-adfd-4933-b626-c411638fd7db

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_arrivalGammaDensity
open MeasureTheory ProbabilityTheory Filter Complex
open scoped ENNReal NNReal

theorem solution
    (lam : ℝ≥0) (w : ℂ) :
    (∑' k : ℕ, ((poissonMeasure lam).real {k} : ℂ) * w ^ k) =
      Complex.exp ((lam : ℝ) * (w - 1)) := by
  have h : ∀ k : ℕ, ((poissonMeasure lam).real {k} : ℂ) * w ^ k
      = (Real.exp (-lam) : ℂ) * (((lam : ℂ) * w) ^ k / (Nat.factorial k : ℂ)) := by
    intro k
    rw [poissonMeasure_real_singleton]
    push_cast
    rw [mul_pow]
    ring
  simp_rw [h]
  rw [tsum_mul_left, (NormedSpace.expSeries_div_hasSum_exp ((lam : ℂ) * w)).tsum_eq,
    ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring
