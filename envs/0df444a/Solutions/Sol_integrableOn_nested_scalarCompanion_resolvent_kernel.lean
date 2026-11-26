-- Prove2me | solution 1 for integrableOn_nested_scalarCompanion_resolvent_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:45.96913+00:00
-- url     : https://prove2.me/submissions/7c09b4b1-fee4-4f66-b90a-3e0ea7e47b61

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Theorems.Thm_SmoothJordanDomain_boundaryParam_mem_resolventSet


set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega Psi : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hnest : closure Omega.carrier ⊆ Psi.carrier) :
    MeasureTheory.IntegrableOn (fun x : ℝ × ℝ =>
      deriv Omega.boundaryParam x.1 •
        (deriv Psi.boundaryParam x.2 •
          (star (Polynomial.eval (Psi.boundaryParam x.2) p) •
            ((2 * (Real.pi : ℂ) * I)⁻¹ •
              ((Psi.boundaryParam x.2 - Omega.boundaryParam x.1)⁻¹ •
                resolvent A (Omega.boundaryParam x.1))))))
      (uIoc (0 : ℝ) (2 * Real.pi) ×ˢ
        uIoc (0 : ℝ) (2 * Real.pi)) := by
  let K : Set (ℝ × ℝ) :=
    Icc (0 : ℝ) (2 * Real.pi) ×ˢ Icc (0 : ℝ) (2 * Real.pi)
  have hOmegaParam : Continuous (fun x : ℝ × ℝ =>
      Omega.boundaryParam x.1) :=
    Omega.boundaryParam_contDiff.continuous.comp continuous_fst
  have hPsiParam : Continuous (fun x : ℝ × ℝ =>
      Psi.boundaryParam x.2) :=
    Psi.boundaryParam_contDiff.continuous.comp continuous_snd
  have hOmegaDeriv : Continuous (fun x : ℝ × ℝ =>
      deriv Omega.boundaryParam x.1) :=
    (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).comp
      continuous_fst
  have hPsiDeriv : Continuous (fun x : ℝ × ℝ =>
      deriv Psi.boundaryParam x.2) :=
    (Psi.boundaryParam_contDiff.continuous_deriv (by norm_num)).comp
      continuous_snd
  have hres : ContinuousOn (fun x : ℝ × ℝ =>
      resolvent A (Omega.boundaryParam x.1)) K := by
    have hresBase : ContinuousOn (resolvent A)
        (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) := by
      rintro z ⟨t, _ht, rfl⟩
      exact (spectrum.hasDerivAt_resolvent_const_left
        (Omega.boundaryParam_mem_resolventSet A hOmega t)).continuousAt.continuousWithinAt
    apply hresBase.comp' hOmegaParam.continuousOn
    intro x hx
    exact ⟨x.1, hx.1, rfl⟩
  have hinv : ContinuousOn (fun x : ℝ × ℝ =>
      (Psi.boundaryParam x.2 - Omega.boundaryParam x.1)⁻¹) K := by
    apply ContinuousOn.inv₀
    · exact hPsiParam.continuousOn.sub hOmegaParam.continuousOn
    · intro x _hx
      apply sub_ne_zero.mpr
      intro heq
      have hInnerFrontier :
          Omega.boundaryParam x.1 ∈ frontier Omega.carrier := by
        rw [← Omega.boundaryParam_range]
        exact mem_range_self x.1
      have hOuterFrontier :
          Psi.boundaryParam x.2 ∈ frontier Psi.carrier := by
        rw [← Psi.boundaryParam_range]
        exact mem_range_self x.2
      have hempty : Psi.boundaryParam x.2 ∈ (∅ : Set ℂ) := by
        rw [← Psi.isOpen_carrier.inter_frontier_eq]
        refine ⟨?_, hOuterFrontier⟩
        rw [heq]
        exact hnest (frontier_subset_closure hInnerFrontier)
      exact hempty.elim
  have hpoly : Continuous (fun x : ℝ × ℝ =>
      star (Polynomial.eval (Psi.boundaryParam x.2) p)) :=
    p.continuous.star.comp hPsiParam
  have hc : ContinuousOn (fun _x : ℝ × ℝ =>
      (2 * (Real.pi : ℂ) * I)⁻¹) K := continuousOn_const
  have hcont : ContinuousOn (fun x : ℝ × ℝ =>
      deriv Omega.boundaryParam x.1 •
        (deriv Psi.boundaryParam x.2 •
          (star (Polynomial.eval (Psi.boundaryParam x.2) p) •
            ((2 * (Real.pi : ℂ) * I)⁻¹ •
              ((Psi.boundaryParam x.2 - Omega.boundaryParam x.1)⁻¹ •
                resolvent A (Omega.boundaryParam x.1)))))) K :=
    hOmegaDeriv.continuousOn.smul
      (hPsiDeriv.continuousOn.smul
        (hpoly.continuousOn.smul
          (hc.smul (hinv.smul hres))))
  apply (hcont.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
  rw [uIoc_of_le Real.two_pi_pos.le]
  exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
