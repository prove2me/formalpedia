-- Prove2me | solution 1 for levy_foundations_semigroup_exponent_normalised_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:47:39.05419+00:00
-- url     : https://prove2.me/submissions/2e4c0ce1-7707-4d2f-86bb-7acd48eaa724

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
theorem solution
    (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hsemigroup : ∀ t : ℝ, 0 ≤ t →
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
        ∀ ξ : ℝ, charFun ν ξ = Complex.exp ((t : ℂ) * ψ ξ)) :
    ψ 0 = 0 ∧
      ∀ ξ : ℝ, ψ (-ξ) = starRingEnd ℂ (ψ ξ) := by
  have ray_zero (z : ℂ)
      (hpos : ∀ t : ℝ, 0 ≤ t →
        Complex.exp ((t : ℂ) * z) = 1) : z = 0 := by
    have hall : ∀ t : ℝ, Complex.exp ((t : ℂ) * z) = 1 := by
      intro t
      by_cases ht : 0 ≤ t
      · exact hpos t ht
      · have hneg := hpos (-t) (neg_nonneg.mpr (le_of_lt (lt_of_not_ge ht)))
        have heq : (t : ℂ) * z = -(((-t : ℝ) : ℂ) * z) := by
          push_cast; ring
        rw [heq, Complex.exp_neg, hneg]
        norm_num
    have hfun :
        (fun t : ℝ =>
            (Complex.exp ((t : ℂ) * z) - 1) / (t : ℂ)) =
          (fun _ => (0 : ℂ)) := by
      funext t; rw [hall t]; simp
    have hg : HasDerivAt (fun t : ℝ => cexp ((↑t : ℂ) * z)) z 0 := by
      have hf : HasDerivAt (fun t : ℝ => (↑t : ℂ) * z) (1 * z) 0 :=
        (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const z
      have hexp := hf.cexp
      simp only [ofReal_zero, zero_mul, exp_zero, one_mul, one_mul] at hexp
      exact hexp
    have hslope := hg.tendsto_slope_zero
    simp only [zero_add, ofReal_zero, zero_mul, exp_zero] at hslope
    have hlim : Tendsto
        (fun t : ℝ => (cexp ((↑t : ℂ) * z) - 1) / (↑t : ℂ))
        (𝓝[≠] (0 : ℝ)) (𝓝 z) := by
      exact hslope.congr (fun t => by
        show t⁻¹ • (cexp ((↑t : ℂ) * z) - 1) =
          (cexp ((↑t : ℂ) * z) - 1) / (↑t : ℂ)
        rw [RCLike.real_smul_eq_coe_mul (K := ℂ)]
        push_cast; rw [inv_mul_eq_div]; norm_cast)
    rw [hfun] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  have hzero : ψ 0 = 0 := by
    apply ray_zero
    intro t ht
    obtain ⟨ν, hν, hchar⟩ := hsemigroup t ht
    letI : IsProbabilityMeasure ν := hν
    have h0 : charFun ν 0 = 1 := by simp [charFun_zero, Measure.real, measure_univ]
    exact (hchar 0).symm.trans h0
  refine ⟨hzero, ?_⟩
  intro ξ
  apply sub_eq_zero.mp
  apply ray_zero
  intro t ht
  obtain ⟨ν, hν, hchar⟩ := hsemigroup t ht
  letI : IsProbabilityMeasure ν := hν
  have hφ :
      Complex.exp ((t : ℂ) * ψ (-ξ)) =
        starRingEnd ℂ (Complex.exp ((t : ℂ) * ψ ξ)) := by
    calc
      _ = charFun ν (-ξ) := (hchar (-ξ)).symm
      _ = starRingEnd ℂ (charFun ν ξ) := by rw [charFun_neg]
      _ = _ := by rw [hchar ξ]
  have hφ' :
      Complex.exp ((t : ℂ) * ψ (-ξ)) =
        Complex.exp ((t : ℂ) * starRingEnd ℂ (ψ ξ)) := by
    calc
      _ = starRingEnd ℂ (Complex.exp ((t : ℂ) * ψ ξ)) := hφ
      _ = Complex.exp (starRingEnd ℂ ((t : ℂ) * ψ ξ)) := by
        rw [Complex.exp_conj]
      _ = _ := by
        congr 1
        simp
  rw [mul_sub, Complex.exp_sub, hφ', div_self (Complex.exp_ne_zero _)]