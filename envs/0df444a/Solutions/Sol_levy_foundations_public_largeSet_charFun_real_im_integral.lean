-- Prove2me | solution 1 for levy_foundations_public_largeSet_charFun_real_im_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:36:37.321374+00:00
-- url     : https://prove2.me/submissions/822d0763-5be4-4656-85a9-b3427ae50322

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal

/-- Split the large-jump characteristic integral into its cosine and sine parts. -/
theorem solution
    (m : Measure ℝ) (ρ ξ : ℝ)
    (hint : IntegrableOn
      (fun x : ℝ => Complex.exp ((↑x : ℂ) * ↑ξ * Complex.I) - 1)
      (ProbabilityTheory.largeSet ρ) m) :
    ∫ x in ProbabilityTheory.largeSet ρ,
      (Complex.exp ((↑x : ℂ) * ↑ξ * Complex.I) - 1) ∂m =
      (↑(∫ x in ProbabilityTheory.largeSet ρ, (Real.cos (x * ξ) - 1) ∂m) : ℂ)
      + (↑(∫ x in ProbabilityTheory.largeSet ρ, Real.sin (x * ξ) ∂m) : ℂ)
        * Complex.I := by
  let F : ℝ → ℂ := fun x => Complex.exp ((↑x : ℂ) * ↑ξ * Complex.I) - 1
  have heuler (x : ℝ) :
      F x = (↑(Real.cos (x * ξ) - 1) : ℂ) +
        (↑(Real.sin (x * ξ)) : ℂ) * Complex.I := by
    dsimp [F]
    have h := Complex.exp_ofReal_mul_I (x * ξ)
    have hmul : (↑(x * ξ) : ℂ) = (↑x : ℂ) * ↑ξ := by push_cast; rfl
    rw [hmul] at h
    rw [h]
    push_cast
    ring
  have hre (x : ℝ) : (F x).re = Real.cos (x * ξ) - 1 := by
    rw [heuler x]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero, mul_one, zero_add]
  have him (x : ℝ) : (F x).im = Real.sin (x * ξ) := by
    rw [heuler x]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero, mul_one, zero_add]
  have hre_int :
      (∫ x in ProbabilityTheory.largeSet ρ, F x ∂m).re =
        ∫ x in ProbabilityTheory.largeSet ρ, Real.cos (x * ξ) - 1 ∂m := by
    calc
      _ = ∫ x in ProbabilityTheory.largeSet ρ, (F x).re ∂m :=
        (integral_re hint).symm
      _ = _ := by simp_rw [hre]
  have him_int :
      (∫ x in ProbabilityTheory.largeSet ρ, F x ∂m).im =
        ∫ x in ProbabilityTheory.largeSet ρ, Real.sin (x * ξ) ∂m := by
    calc
      _ = ∫ x in ProbabilityTheory.largeSet ρ, (F x).im ∂m :=
        (integral_im hint).symm
      _ = _ := by simp_rw [him]
  change (∫ x in ProbabilityTheory.largeSet ρ, F x ∂m) =
      (↑(∫ x in ProbabilityTheory.largeSet ρ, Real.cos (x * ξ) - 1 ∂m) : ℂ)
        + (↑(∫ x in ProbabilityTheory.largeSet ρ, Real.sin (x * ξ) ∂m) : ℂ) * Complex.I
  apply Complex.ext
  · simpa [Complex.add_re, Complex.mul_re] using hre_int
  · simpa [Complex.add_im, Complex.mul_im] using him_int
