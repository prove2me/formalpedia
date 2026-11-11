-- Prove2me | solution 1 for levy_foundations_semigroup_one_infinitely_divisible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:27:45.808756+00:00
-- url     : https://prove2.me/submissions/ff18dd31-a88f-4941-a63d-e55302579f19

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_levy_foundations_iteratedConv
import Definitions.Def_levy_foundations_iteratedConvolutionPower
import Theorems.Thm_levy_foundations_charFun_iteratedConvolutionPower

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex

/-- A time-one member of an exponential characteristic semigroup admits
a convolution root of every positive order. -/
theorem solution
    (ψ : ℝ → ℂ)
    (hsemigroup : ∀ t : ℝ, 0 ≤ t →
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
        ∀ ξ : ℝ, charFun ν ξ = Complex.exp ((t : ℂ) * ψ ξ)) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      LevyFoundations.isInfinitelyDivisible μ ∧
      ∀ ξ : ℝ, charFun μ ξ = Complex.exp (ψ ξ) := by
  obtain ⟨μ, hμ, hμchar⟩ := hsemigroup 1 (by norm_num)
  refine ⟨μ, hμ, ?_, ?_⟩
  · intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hnzero : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have ht : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hnpos.le
    obtain ⟨ν, hν, hνchar⟩ := hsemigroup (n : ℝ)⁻¹ ht
    refine ⟨ν, hν, ?_⟩
    letI : IsProbabilityMeasure μ := hμ
    letI : IsProbabilityMeasure ν := hν
    have hcompat : ∀ k : ℕ,
        LevyFoundations.iteratedConvolutionPower ν k =
          LevyFoundations.iteratedConv ν k := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
          change ν ∗ LevyFoundations.iteratedConvolutionPower ν k =
            ν ∗ LevyFoundations.iteratedConv ν k
          rw [ih]
    have hncomplex : (n : ℂ) ≠ 0 := by exact_mod_cast hnzero
    have hscale (ξ : ℝ) :
        (n : ℂ) * ((↑((n : ℝ)⁻¹) : ℂ) * ψ ξ) = ψ ξ := by
      rw [Complex.ofReal_inv]
      calc
        _ = ((n : ℂ) * (n : ℂ)⁻¹) * ψ ξ := (mul_assoc _ _ _).symm
        _ = ψ ξ := by simp [hncomplex]
    have hfinite : ∀ k : ℕ,
        IsFiniteMeasure (LevyFoundations.iteratedConv ν k) := by
      intro k
      induction k with
      | zero =>
          dsimp [LevyFoundations.iteratedConv]
          infer_instance
      | succ k ih =>
          change IsFiniteMeasure (ν ∗ LevyFoundations.iteratedConv ν k)
          letI : IsFiniteMeasure (LevyFoundations.iteratedConv ν k) := ih
          infer_instance
    letI : IsFiniteMeasure (LevyFoundations.iteratedConv ν n) := hfinite n
    apply Measure.ext_of_charFun
    funext ξ
    calc
      charFun μ ξ = Complex.exp (ψ ξ) := by simpa using hμchar ξ
      _ = Complex.exp ((n : ℂ) * ((↑((n : ℝ)⁻¹) : ℂ) * ψ ξ)) := by
        rw [hscale ξ]
      _ = (Complex.exp ((↑((n : ℝ)⁻¹) : ℂ) * ψ ξ)) ^ n := by
        rw [Complex.exp_nat_mul]
      _ = charFun (LevyFoundations.iteratedConv ν n) ξ := by
        rw [← hcompat n, levy_foundations_charFun_iteratedConvolutionPower ν n ξ, hνchar ξ]
  · intro ξ
    simpa using hμchar ξ
