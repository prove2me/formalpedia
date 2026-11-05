-- Prove2me | solution 1 for levy_foundations_arrivalGammaDensityConvolution
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:10:05.697992+00:00
-- url     : https://prove2.me/submissions/ae4bf5b6-a542-49be-bfc7-3c45f8949e64

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
    {R : ℝ} (hR : 0 < R) (n : ℕ) (z : ℝ) :
    (∫⁻ x, LevyFoundations.arrivalGammaDensity R n x *
      LevyFoundations.arrivalGammaDensity R 0 (z - x)) =
       LevyFoundations.arrivalGammaDensity R (n + 1) z := by
  unfold LevyFoundations.arrivalGammaDensity LevyFoundations.arrivalGammaDensityReal
  by_cases hz : z < 0
  · have hzi : z ∉ Set.Ici (0 : ℝ) := by simpa using hz
    rw [Set.indicator_of_notMem hzi]
    calc (∫⁻ x, (Set.Ici (0 : ℝ)).indicator
            (fun y => ENNReal.ofReal (R ^ (n + 1) * y ^ n * Real.exp (-(R * y)) / ↑n.factorial)) x *
          (Set.Ici (0 : ℝ)).indicator
            (fun y => ENNReal.ofReal (R ^ (0 + 1) * y ^ 0 * Real.exp (-(R * y)) / ↑(Nat.factorial 0))) (z - x))
        = ∫⁻ _ : ℝ, 0 := by
          refine lintegral_congr fun x => ?_
          by_cases hx : 0 ≤ x
          · have : z - x ∉ Set.Ici (0 : ℝ) := by simp; linarith
            rw [Set.indicator_of_notMem this, mul_zero]
          · have : x ∉ Set.Ici (0 : ℝ) := by simpa using hx
            rw [Set.indicator_of_notMem this, zero_mul]
      _ = 0 := lintegral_zero
  · push Not at hz
    set c : ℝ := R ^ (n + 2) * Real.exp (-(R * z)) / ↑n.factorial with hc
    have hc0 : 0 ≤ c := by positivity
    have step1 : ∀ x : ℝ, ((Set.Ici (0 : ℝ)).indicator
            (fun y => ENNReal.ofReal (R ^ (n + 1) * y ^ n * Real.exp (-(R * y)) / ↑n.factorial)) x *
          (Set.Ici (0 : ℝ)).indicator
            (fun y => ENNReal.ofReal (R ^ (0 + 1) * y ^ 0 * Real.exp (-(R * y)) / ↑(Nat.factorial 0))) (z - x))
        = (Set.Icc (0 : ℝ) z).indicator (fun x => ENNReal.ofReal (c * x ^ n)) x := by
      intro x
      by_cases hx : x ∈ Set.Icc (0 : ℝ) z
      · obtain ⟨hx0, hxz⟩ := hx
        have h1 : x ∈ Set.Ici (0 : ℝ) := hx0
        have h2 : z - x ∈ Set.Ici (0 : ℝ) := by simp; linarith
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
          Set.indicator_of_mem (show x ∈ Set.Icc (0 : ℝ) z from ⟨hx0, hxz⟩), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have e : Real.exp (-(R * x)) * Real.exp (-(R * (z - x))) = Real.exp (-(R * z)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [hc, ← e]
        simp
        ring
      · rw [Set.indicator_of_notMem hx]
        by_cases hx0 : 0 ≤ x
        · have : z - x ∉ Set.Ici (0 : ℝ) := by
            simp
            by_contra h
            exact hx ⟨hx0, by linarith⟩
          rw [Set.indicator_of_notMem this, mul_zero]
        · have : x ∉ Set.Ici (0 : ℝ) := by simpa using hx0
          rw [Set.indicator_of_notMem this, zero_mul]
    simp_rw [step1]
    rw [lintegral_indicator measurableSet_Icc]
    have hint : IntegrableOn (fun x : ℝ => c * x ^ n) (Set.Icc 0 z) :=
      (by fun_prop : Continuous fun x : ℝ => c * x ^ n).integrableOn_Icc
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) z)] fun x : ℝ => c * x ^ n :=
      (ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun x hx => by have := hx.1; positivity)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hz,
      intervalIntegral.integral_const_mul, integral_pow]
    have h1 : z ∈ Set.Ici (0 : ℝ) := hz
    rw [Set.indicator_of_mem h1]
    congr 1
    rw [hc]
    push_cast [Nat.factorial_succ]
    field_simp
    simp
