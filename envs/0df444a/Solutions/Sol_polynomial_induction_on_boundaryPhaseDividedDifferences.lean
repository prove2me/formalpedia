-- Prove2me | solution 1 for polynomial_induction_on_boundaryPhaseDividedDifferences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:41.347715+00:00
-- url     : https://prove2.me/submissions/92540002-7748-4803-b54a-fcf5d1947d89

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_natDegree_divByMonic_X_sub_C_lt
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
theorem _root_.solution
    (Omega : SmoothJordanDomain) (P : Polynomial ℂ → Prop)
    (hzero : ∀ p, p.natDegree = 0 → P p)
    (hstep : ∀ p, 0 < p.natDegree →
      (∀ xi ∈ frontier Omega.carrier,
        P (p /ₘ (Polynomial.X - Polynomial.C xi))) →
      P p) :
    ∀ p, P p := by
  intro p
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
      by_cases hp : p.natDegree = 0
      · exact hzero p hp
      · apply hstep p (Nat.pos_of_ne_zero hp)
        intro xi _hxi
        apply ih
          (p /ₘ (Polynomial.X - Polynomial.C xi)).natDegree
        · simpa only [← hn] using
            natDegree_divByMonic_X_sub_C_lt p xi
              (Nat.pos_of_ne_zero hp)
        · rfl
