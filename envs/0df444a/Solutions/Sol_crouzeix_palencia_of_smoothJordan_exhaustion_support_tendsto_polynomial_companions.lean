-- Prove2me | solution 1 for crouzeix_palencia_of_smoothJordan_exhaustion_support_tendsto_polynomial_companions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:24:54.456571+00:00
-- url     : https://prove2.me/submissions/2fcc97b6-286e-43b9-a185-4ffd7dc46d3b

import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Theorems.Thm_crouzeix_palencia_of_smoothJordan_exhaustion_oriented_support_tendsto_polynomial_companions
import Theorems.Thm_canonicalNormal_support_all_of_Ioc
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_polynomialSupNorm_nonneg
import Theorems.Thm_spectrum_subset_closure_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (hfrontier : ∀ n, frontier (Omega n).carrier ⊆ K n)
    (hOmega : ∀ n, closure (numericalRange A) ⊆ (Omega n).carrier)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (hcompanion : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ q : ℕ → Polynomial ℂ,
        (∀ j, polynomialSupNorm (q j) (K n) ≤
          polynomialSupNorm p (K n)) ∧
        Tendsto (fun j => Polynomial.aeval A (q j)) atTop
          (nhds (crouzeixPolynomialAuxiliaryOperator A (Omega n) p))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    constructor
    · exact spectrum_subset_closure_numericalRange A
    · intro p
      have hzero : Polynomial.aeval A p = 0 := Subsingleton.elim _ _
      rw [hzero, norm_zero]
      exact mul_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg 2))
        (polynomialSupNorm_nonneg p (closure (numericalRange A)))
  · let _ := hE
    obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have hxnorm : ‖x‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right] at hx
      exact hx
    let c : ℂ := ⟪x, A x⟫_ℂ
    have hcW : c ∈ numericalRange A :=
      (mem_numericalRange A c).mpr ⟨x, hxnorm, rfl⟩
    apply
      crouzeix_palencia_of_smoothJordan_exhaustion_oriented_support_tendsto_polynomial_companions
        A Omega K hanti hcompact hnonempty hinter hfrontier hOmega hsupport
    · intro n
      refine ⟨c, hOmega n (subset_closure hcW), ?_⟩
      apply canonicalNormal_support_all_of_Ioc
      intro t ht
      exact hsupport n t ht c hcW
    · exact hcompanion
