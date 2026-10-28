-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_killed_discounted_expectation_le_of_local_generator_upper_deriv
-- name    : AvramDividend.Classical.levy_killed_discounted_expectation_le_of_local_generator_upper_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:20:50.631925+00:00
-- url     : https://prove2.me/theorems/d6f8a4e2-96f5-46f9-9b83-ac18d3b595f1
-- title:
--   Stopped HJB domination from a one-sided killed generator derivative bound
-- statement:
--   Suppose the killed expected reward f(s) is continuously extendable to time zero, differentiable at positive times, and its derivative is bounded above by the expected killed generator. On active states only, assume the generator HJB inequality Gamma w <= q w and integrability of the killed test rewards. Then exp(-qt) f(t) <= f(0). Unlike the exact generator identity, a one-sided upper inequality accommodates additional nonpositive boundary flux from stopping or killing. The stochastic task is to establish this upper Dynkin inequality for the stopped controlled Lévy reserve, including its dividend terms.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), stopped Ito/localisation estimate in Section 5.4.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_discounted_semigroup_le_initial_of_deriv_le

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_killed_discounted_expectation_le_of_local_generator_upper_deriv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (q : ℝ) (z : ℝ → Ω → ℝ)
    (active : ℝ → Ω → Bool) (f : ℝ → ℝ)
    (hfcont : ContinuousOn f (Ici 0))
    (hfdiff : ∀ s : ℝ, 0 < s → DifferentiableAt ℝ f s)
    (hftrans : ∀ s : ℝ, 0 < s →
      f s = ∫ ω, if active s ω then w (z s ω) else 0 ∂P)
    (hfderivLe : ∀ s : ℝ, 0 < s →
      deriv f s ≤ ∫ ω,
        if active s ω then X.generator w (z s ω) else 0 ∂P)
    (hIntW : ∀ s : ℝ, 0 < s → Integrable
      (fun ω => if active s ω then w (z s ω) else 0) P)
    (hIntGen : ∀ s : ℝ, 0 < s → Integrable
      (fun ω => if active s ω then X.generator w (z s ω) else 0) P)
    (hHJB : ∀ s : ℝ, 0 < s → ∀ ω, active s ω = true →
      X.generator w (z s ω) ≤ q * w (z s ω))
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-(q * t)) * f t ≤ f 0 := by sorry
