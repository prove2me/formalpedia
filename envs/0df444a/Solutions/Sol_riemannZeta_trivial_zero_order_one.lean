-- Prove2me | solution 1 for riemannZeta_trivial_zero_order_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:40:11.781779+00:00
-- url     : https://prove2.me/submissions/9c31546a-791a-466b-a86c-8774a4f16912

import Mathlib
import Theorems.Thm_invGammaR_neg_even_deriv_ne_zero

open Complex Topology Filter Set

theorem solution (n : ℕ) :
    analyticOrderAt riemannZeta (-2 * ((n + 1 : ℕ) : ℂ)) = (1 : ℕ∞) := by
  let a : ℂ := -2 * ((n + 1 : ℕ) : ℂ)
  let t : ℂ := 1 - a
  let C : ℂ → ℂ := completedRiemannZeta
  let R : ℂ → ℂ := fun s => (Gammaℝ s)⁻¹
  have ha0 : a ≠ 0 := by
    dsimp [a]
    exact mul_ne_zero (by norm_num) (by exact_mod_cast Nat.succ_ne_zero n)
  have ha1 : a ≠ 1 := by
    intro ha
    have hre := congrArg Complex.re ha
    norm_num [a] at hre
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith
  have ht_re : 1 ≤ t.re := by
    dsimp [t, a]
    norm_num
    positivity
  have ht0 : t ≠ 0 := by
    intro ht
    have hre := congrArg Complex.re ht
    norm_num at hre
    linarith
  have hCa : C a ≠ 0 := by
    intro hzero
    have hCt : C t = 0 := by
      dsimp [C, t]
      rw [completedRiemannZeta_one_sub]
      exact hzero
    have hzeta_t : riemannZeta t = 0 := by
      rw [riemannZeta_def_of_ne_zero ht0]
      simp [C] at hCt
      rw [hCt, zero_div]
    exact riemannZeta_ne_zero_of_one_le_re ht_re hzeta_t
  have hRa : R a = 0 := by
    have hgamma : Gammaℝ a = 0 := by
      rw [Gammaℝ_eq_zero_iff]
      refine ⟨n + 1, ?_⟩
      dsimp [a]
      push_cast
      ring
    simp [R, hgamma]
  have hRderiv : deriv R a ≠ 0 := by
    simpa [R, a] using invGammaR_neg_even_deriv_ne_zero n
  have hlocal : riemannZeta =ᶠ[𝓝 a] C * R := by
    filter_upwards [eventually_ne_nhds ha0] with z hz
    rw [riemannZeta_def_of_ne_zero hz]
    simp [C, R, div_eq_mul_inv]
  have hCdiff : DifferentiableAt ℂ C a := by
    simpa [C] using differentiableAt_completedZeta ha0 ha1
  have hRdiff : DifferentiableAt ℂ R a := by
    exact differentiable_Gammaℝ_inv a
  have hprod := hCdiff.hasDerivAt.mul hRdiff.hasDerivAt
  have hzeta_deriv : deriv riemannZeta a ≠ 0 := by
    rw [hlocal.deriv_eq, hprod.deriv, hRa, mul_zero, zero_add]
    exact mul_ne_zero hCa hRderiv
  have hzeta : riemannZeta a = 0 := by
    simpa [a] using riemannZeta_neg_two_mul_nat_add_one n
  have han : AnalyticAt ℂ riemannZeta a :=
    analyticOn_riemannZeta a (by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using ha1)
  simpa [a] using han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzeta hzeta_deriv
