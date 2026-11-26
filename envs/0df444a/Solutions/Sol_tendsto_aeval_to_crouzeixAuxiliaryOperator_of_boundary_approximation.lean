-- Prove2me | solution 1 for tendsto_aeval_to_crouzeixAuxiliaryOperator_of_boundary_approximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:40.411543+00:00
-- url     : https://prove2.me/submissions/0b479528-1ddb-43de-9c83-d3d1c516b3ef

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionConvergence
import Theorems.Thm_contourIntegral_sub
import Theorems.Thm_crouzeixAuxiliaryIntegrand_contourIntegrable
import Theorems.Thm_exists_bound_crouzeixPolynomialAuxiliaryIntegrand
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_contourIntegral_le_of_norm_le_const
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (g : ℂ → ℂ)
    (q : ℕ → Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hg : ContinuousOn g
      (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)))
    (hCauchy : ∀ j, Polynomial.aeval A (q j) =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral
          (fun z ↦ Polynomial.eval z (q j) • resolvent A z)
          Omega.boundaryParam)
    (happrox : ∀ (j : ℕ) (t : ℝ),
      t ∈ Icc (0 : ℝ) (2 * Real.pi) →
      ‖Polynomial.eval (Omega.boundaryParam t) (q j) -
        g (Omega.boundaryParam t)‖ ≤
          1 / ((j : ℝ) + 1)) :
    Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop
      (nhds (crouzeixAuxiliaryOperator A Omega g)) := by
  obtain ⟨C, hC⟩ :=
    exists_bound_crouzeixPolynomialAuxiliaryIntegrand A Omega
      (Polynomial.C 1) hOmega
  have hkernel : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t •
        resolvent A (Omega.boundaryParam t)‖ ≤ C := by
    intro t ht
    simpa only [Polynomial.eval_C, star_one, one_smul] using hC t ht
  have hC0 : 0 ≤ C :=
    (norm_nonneg (deriv Omega.boundaryParam 0 •
      resolvent A (Omega.boundaryParam 0))).trans
      (hkernel 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  let D : ℝ := ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C)
  have hdist : ∀ j, dist (Polynomial.aeval A (q j))
      (crouzeixAuxiliaryOperator A Omega g) ≤
        D * (1 / ((j : ℝ) + 1)) := by
    intro j
    have hqint : ContourIntegrable
        (fun z ↦ Polynomial.eval z (q j) • resolvent A z)
        Omega.boundaryParam :=
      crouzeixAuxiliaryIntegrand_contourIntegrable A Omega
        (fun z ↦ Polynomial.eval z (q j)) hOmega
          (q j).continuous.continuousOn
    have hgint :=
      crouzeixAuxiliaryIntegrand_contourIntegrable A Omega g hOmega hg
    have hintegrand : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
        ‖deriv Omega.boundaryParam t •
          ((Polynomial.eval (Omega.boundaryParam t) (q j) -
              g (Omega.boundaryParam t)) •
            resolvent A (Omega.boundaryParam t))‖ ≤
          (1 / ((j : ℝ) + 1)) * C := by
      intro t ht
      rw [smul_smul, norm_smul, norm_mul]
      calc
        ‖deriv Omega.boundaryParam t‖ *
            ‖Polynomial.eval (Omega.boundaryParam t) (q j) -
              g (Omega.boundaryParam t)‖ *
              ‖resolvent A (Omega.boundaryParam t)‖ =
            ‖Polynomial.eval (Omega.boundaryParam t) (q j) -
              g (Omega.boundaryParam t)‖ *
              ‖deriv Omega.boundaryParam t •
                resolvent A (Omega.boundaryParam t)‖ := by
          rw [norm_smul]
          ring
        _ ≤ (1 / ((j : ℝ) + 1)) * C :=
          mul_le_mul (happrox j t ht) (hkernel t ht) (norm_nonneg _) (by positivity)
    rw [dist_eq_norm, hCauchy j]
    unfold crouzeixAuxiliaryOperator
    rw [← smul_sub, ← contourIntegral_sub hqint hgint]
    simp only [← sub_smul]
    change ‖(2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral
          (fun z ↦ (Polynomial.eval z (q j) -
            g z) • resolvent A z)
          Omega.boundaryParam‖ ≤ D * (1 / ((j : ℝ) + 1))
    rw [norm_smul]
    calc
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          ‖contourIntegral
            (fun z ↦ (Polynomial.eval z (q j) -
              g z) • resolvent A z)
            Omega.boundaryParam‖ ≤
          ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
            (2 * Real.pi * ((1 / ((j : ℝ) + 1)) * C)) :=
        mul_le_mul_of_nonneg_left
          (norm_contourIntegral_le_of_norm_le_const hintegrand) (norm_nonneg _)
      _ = D * (1 / ((j : ℝ) + 1)) := by
        simp only [D]
        ring
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ ↦ dist_nonneg) hdist
  have heps : Tendsto (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [mul_zero] using tendsto_const_nhds.mul heps
