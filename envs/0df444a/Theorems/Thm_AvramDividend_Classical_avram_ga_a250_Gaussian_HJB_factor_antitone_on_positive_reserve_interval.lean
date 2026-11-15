-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a250_Gaussian_HJB_factor_antitone_on_positive_reserve_interval
-- name    : AvramDividend.Classical.avram_ga_a250_Gaussian_HJB_factor_antitone_on_positive_reserve_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:09:21.287934+00:00
-- url     : https://prove2.me/theorems/b15b7378-3596-4931-82b9-3b297c1c6d5f
-- title:
--   Gaussian HJB positive-reserve exponentially weighted first-order factor antitone under scalar super-solution inequality
-- statement:
--   For the original zerojump Gaussian HJB scalar super-solution, if a function is C² on a strictly positive-reserve interval and its factorised ODE second-order expression is nonpositive, the exponentially weighted first-order factor exp(-lambdaMinus t)(f prime(t)-lambdaPlus f(t)) is antitone on every compact interior [y,a] with 0<y≤a. Consequently its value at y is at least the value at a. This derivative-sign argument is essential for a uniform candidate-value upper bound near zero without needing w(0), and eventually for original a216.
-- source:
--   Gaussian HJB factor derivative a249 and Mathlib antitoneOn_of_deriv_nonpos, positive reserve scalar ODE

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a249_Gaussian_HJB_factor_exponential_derivative
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a250_Gaussian_HJB_factor_antitone_on_positive_reserve_interval
    (f fp fpp : ℝ → ℝ) (lambdaPlus lambdaMinus a y : ℝ)
    (hy : 0 < y) (hya : y ≤ a)
    (hf : ∀ t ∈ Set.Ioo 0 a, HasDerivAt f (fp t) t)
    (hfp : ∀ t ∈ Set.Ioo 0 a, HasDerivAt fp (fpp t) t)
    (hCont : ContinuousOn (fun t =>
      Real.exp (-lambdaMinus*t)*(fp t-lambdaPlus*f t))
      (Set.Icc y a))
    (hOde : ∀ t ∈ Set.Ioo 0 a,
      fpp t-(lambdaPlus+lambdaMinus)*fp t+
        lambdaPlus*lambdaMinus*f t ≤ 0) :
    Real.exp (-lambdaMinus*a)*(fp a-lambdaPlus*f a) ≤
    Real.exp (-lambdaMinus*y)*(fp y-lambdaPlus*f y) := by sorry
