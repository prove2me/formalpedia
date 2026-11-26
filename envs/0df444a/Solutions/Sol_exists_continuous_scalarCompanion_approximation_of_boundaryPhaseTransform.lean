-- Prove2me | solution 1 for exists_continuous_scalarCompanion_approximation_of_boundaryPhaseTransform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:43:40.060467+00:00
-- url     : https://prove2.me/submissions/24c22231-6000-4585-be07-fe560f572b71

import Definitions.Def_Operator_Crouzeix_BoundaryApproximation
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform
import Theorems.Thm_polynomialSupNorm_closure_carrier_eq_frontier


set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
omit [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (hreg : ∀ xi ∈ frontier Omega.carrier,
      Tendsto
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)))
    (hphase : ∀ xi ∈ frontier Omega.carrier,
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform Omega xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier Omega.carrier))
    (r : ℕ → Polynomial ℂ)
    (happrox : ∀ (j : ℕ) (z : ℂ), z ∈ closure Omega.carrier →
      ‖Polynomial.eval z (r j) -
          crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
        1 / ((j : ℝ) + 1))
    (hPlemelj :
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p) :
    ∃ (g : ℂ → ℂ) (q : ℕ → Polynomial ℂ),
      ContinuousOn g
          (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi)) ∧
      (∀ z ∈ closure Omega.carrier,
        ‖g z‖ ≤ polynomialSupNorm p (closure Omega.carrier)) ∧
      (∀ (j : ℕ) (z : ℂ), z ∈ closure Omega.carrier →
        ‖Polynomial.eval z (q j) - g z‖ ≤ 1 / ((j : ℝ) + 1)) ∧
      crouzeixAuxiliaryOperator A Omega g =
        crouzeixPolynomialAuxiliaryOperator A Omega p := by
  refine ⟨
    crouzeixPolynomialScalarCompanionClosedExtension Omega p,
    r, ?_, ?_, happrox, hPlemelj⟩
  · apply
      (continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized
        Omega p hkernel hreg).mono
    rintro z ⟨t, _ht, rfl⟩
    apply frontier_subset_closure
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  · intro z hz
    calc
      ‖crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ ≤
          polynomialSupNorm p (frontier Omega.carrier) :=
        norm_crouzeixPolynomialScalarCompanionClosedExtension_le_of_boundaryPhaseTransform
          Omega p hbounded hkernel hreg hphase hz
      _ = polynomialSupNorm p (closure Omega.carrier) :=
        (polynomialSupNorm_closure_carrier_eq_frontier
          Omega p hbounded).symm
