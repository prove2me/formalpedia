-- Prove2me | solution 2 for levy_foundations_semigroup_exponent_conditionally_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T09:18:01.948334+00:00
-- url     : https://prove2.me/submissions/bc9290c6-6a86-4185-851f-03045275fd1e

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.Calculus.Deriv.Slope
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology

/-- Positive semidefinite characteristic matrices have a positive
infinitesimal quadratic form at the identity. -/
theorem solution
    (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hsemigroup : ∀ t : ℝ, 0 ≤ t →
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
        ∀ ξ : ℝ, charFun ν ξ = Complex.exp ((t : ℂ) * ψ ξ)) :
    ProbabilityTheory.IsConditionallyNegativeDefinite ψ := by
  intro n ξ c hc
  let F : ℝ → ℂ := fun t =>
    ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * Complex.exp ((t : ℂ) * ψ (ξ i - ξ j))
  have hFzero : F 0 = 0 := by
    simp only [F, ofReal_zero, zero_mul, exp_zero, mul_one]
    simp_rw [← Finset.mul_sum]
    simp [hc]
  have hFderiv : HasDerivAt F
      (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j * ψ (ξ i - ξ j)) 0 := by
    dsimp [F]
    apply HasDerivAt.fun_sum
    intro i hi
    apply HasDerivAt.fun_sum
    intro j hj
    have hf : HasDerivAt
        (fun t : ℝ => (t : ℂ) * ψ (ξ i - ξ j))
        (1 * ψ (ξ i - ξ j)) 0 :=
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const
        (ψ (ξ i - ξ j))
    have houter := hf.cexp
    simp only [ofReal_zero, zero_mul, exp_zero, one_mul] at houter
    have h := houter.const_mul (starRingEnd ℂ (c i) * c j)
    simpa only [mul_assoc] using h
  have hlim : Tendsto
      (fun t : ℝ => (t⁻¹ • (F t - F 0)).re)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j * ψ (ξ i - ξ j)).re) := by
    have hs := hFderiv.tendsto_slope_zero
    have hs' := hs.mono_left (nhdsGT_le_nhdsNE 0)
    exact (Complex.continuous_re.continuousAt.tendsto.comp hs').congr
      (fun t => by simp)
  have hnonneg : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ (t⁻¹ • (F t - F 0)).re := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    obtain ⟨ν, hν, hchar⟩ := hsemigroup t ht.le
    letI : IsProbabilityMeasure ν := hν
    let P : ProbabilityMeasure ℝ := ⟨ν, hν⟩
    have hpd := MeasureTheory.ProbabilityMeasure.characteristicFun_positiveSemiDefinite
      P ξ c
    simp only [MeasureTheory.ProbabilityMeasure.characteristicFun_def,
      show (↑P : Measure ℝ) = ν from rfl] at hpd
    simp_rw [hchar] at hpd
    have hFpos : 0 ≤ (F t).re := by simpa only [F] using hpd
    rw [hFzero, sub_zero, RCLike.real_smul_eq_coe_mul (K := ℂ)]
    rw [Complex.mul_re]
    simpa using (mul_nonneg (inv_nonneg.mpr ht.le) hFpos)
  exact ge_of_tendsto hlim hnonneg
