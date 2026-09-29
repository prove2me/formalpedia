-- Prove2me | solution 1 for invGammaR_neg_even_deriv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:32:47.160255+00:00
-- url     : https://prove2.me/submissions/ec2588c6-3a48-4e94-96fd-84516e03ba07

import Mathlib
import Theorems.Thm_invGamma_neg_nat_deriv_ne_zero

open Complex

theorem solution (n : ℕ) :
    deriv (fun s : ℂ => (Gammaℝ s)⁻¹) (-2 * ((n + 1 : ℕ) : ℂ)) ≠ 0 := by
  let a : ℂ := -2 * ((n + 1 : ℕ) : ℂ)
  let J : ℂ → ℂ := fun s => (Gamma s)⁻¹
  let A : ℂ → ℂ := fun s => ((Real.pi : ℂ) ^ (-s / 2))⁻¹
  let B : ℂ → ℂ := J ∘ fun s => id s / 2
  let F : ℂ → ℂ := fun s => (Gammaℝ s)⁻¹
  have hJ : Differentiable ℂ J := differentiable_one_div_Gamma
  have hA : Differentiable ℂ A := by
    dsimp [A]
    apply Differentiable.inv
    · exact (differentiable_id.neg.div_const (2 : ℂ)).const_cpow
        (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
    · intro s
      exact (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero)))
  have hB : Differentiable ℂ B :=
    hJ.comp (differentiable_id.div_const 2)
  have heq : F = A * B := by
    funext s
    simp [F, A, B, J, Gammaℝ_def, mul_inv, mul_comm]
  have ha_div : a / 2 = -((n + 1 : ℕ) : ℂ) := by
    dsimp [a]
    ring
  have hBa : B a = 0 := by
    change (Gamma (a / 2))⁻¹ = 0
    rw [ha_div, Gamma_neg_nat_eq_zero]
    simp
  have hAa : A a ≠ 0 := by
    simp [A, cpow_ne_zero_iff, Real.pi_ne_zero]
  have hcomp := hJ.differentiableAt.hasDerivAt.comp a ((hasDerivAt_id a).div_const 2)
  have hBderiv : deriv B a ≠ 0 := by
    change deriv (J ∘ fun s : ℂ => id s / 2) a ≠ 0
    rw [hcomp.deriv]
    apply mul_ne_zero
    · simpa [J, ha_div] using invGamma_neg_nat_deriv_ne_zero (n + 1)
    · norm_num
  have hprod := (hA a).hasDerivAt.mul (hB a).hasDerivAt
  have hfinal : deriv F a ≠ 0 := by
    rw [congrArg (fun f : ℂ → ℂ => deriv f a) heq]
    rw [hprod.deriv, hBa, mul_zero, zero_add]
    exact mul_ne_zero hAa hBderiv
  simpa [F, a] using hfinal
