-- Prove2me | solution 1 for crouzeix_palencia_of_strictNestedSmoothJordanExhaustion_canonicalOrientation_scalarCompanion_tendstoUniformlyOn_radial_vanishingAtZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:37.039772+00:00
-- url     : https://prove2.me/submissions/5c9480a8-361f-44be-b638-1c83687fbf01

import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Theorems.Thm_crouzeix_palencia_of_smoothJordan_exhaustion_canonicalOrientation_nested_scalarCompanion_tendstoUniformlyOn_radial_vanishingAtZero

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E)
    (Omega : StrictNestedSmoothJordanExhaustion
      (closure (numericalRange A)))
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ q : ℕ → Polynomial ℂ,
        TendstoUniformlyOn
          (fun j z ↦ Polynomial.eval z (q j))
          (crouzeixPolynomialScalarCompanionClosedExtension
            (Omega.domain n).canonicalOrientation p)
          atTop (closure (Omega.domain n).carrier)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  let K : ℕ → Set ℂ := fun n ↦ closure (Omega.domain n).carrier
  have hanti : Antitone K := by
    apply antitone_nat_of_succ_le
    intro n
    exact (Omega.closure_succ_subset n).trans subset_closure
  have hnonempty : ∀ n, (K n).Nonempty := fun n ↦
    (Omega.domain n).carrier_nonempty.mono subset_closure
  apply
    crouzeix_palencia_of_smoothJordan_exhaustion_canonicalOrientation_nested_scalarCompanion_tendstoUniformlyOn_radial_vanishingAtZero
      A Omega.domain K hanti Omega.isCompact_closure hnonempty
        Omega.iInter_closure (fun _ ↦ rfl) Omega.target_subset
          Omega.closure_succ_subset
  exact happrox
