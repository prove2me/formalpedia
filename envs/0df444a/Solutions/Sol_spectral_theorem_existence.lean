-- Prove2me | solution 1 for spectral_theorem_existence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:06:07.9166+00:00
-- url     : https://prove2.me/submissions/5c98c9bf-83cb-44e5-8970-b3fa864cc86d

import Definitions.Def_Spectral_Cayley_Inverse
import Definitions.Def_Spectral_PVM_Unbounded
import Definitions.Def_Spectral_Spectral_CayleyCalculus
import Definitions.Def_Spectral_Spectral_Polarization
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Spectral_Spectral_Existence
import Theorems.Thm_inverseCayleyPVM_integral_cayleyCoordinate
import Theorems.Thm_PVM_coordinate_unboundedIntegral_isFormalAdjoint
import Theorems.Thm_PVM_selfAdjoint_le_coordinate_unboundedIntegral_of_cayley
import Theorems.Thm_PVM_simpleIntegral_one
import Theorems.Thm_PVM_simpleIntegral_zero
import Theorems.Thm_cayleyTransform_unitary
import Theorems.Thm_eq_of_selfAdjoint_le_formalSelfAdjoint
import Theorems.Thm_one_not_mem_eigenvalues_cayleyTransform
attribute [local simp] PVM.simpleIntegral_one
attribute [local simp] PVM.simpleIntegral_zero


section
open MeasureTheory
open CompactlySupported
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem cayleyCoordinate_relation (t : ℝ) :
    (t : ℂ) * (1 - cayleyCoordinate t) =
      Complex.I * (1 + cayleyCoordinate t) := by
  have hden : (t : ℂ) + Complex.I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im,
      zero_add, Complex.zero_im] at him
    exact one_ne_zero him
  rw [cayleyCoordinate]
  field_simp
  ring
end

set_option autoImplicit false
open MeasureTheory
open CompactlySupported
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ E_pvm : PVM E,
      E_pvm.unboundedIntegral ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable = A := by
  let U := cayleyTransform A hA
  have hunit : U ∈ unitary (E →L[ℂ] E) := cayleyTransform_unitary A hA
  have hU : IsStarNormal U :=
    (unitary_iff_isStarNormal_and_spectrum_subset_unitary.mp hunit).1
  have hNoFixed : ∀ x, U x = x → x = 0 :=
    one_not_mem_eigenvalues_cayleyTransform A hA
  let P := inverseCayleyPVM U hU
  let B := P.unboundedIntegral ((↑) : ℝ → ℂ)
    Complex.continuous_ofReal.measurable
  refine ⟨P, ?_⟩
  change B = A
  have hphase : P.integral cayleyCoordinate cayleyCoordinate_measurable
      cayleyCoordinate_bounded = U := by
    exact inverseCayleyPVM_integral_cayleyCoordinate U hU hunit hNoFixed
  have hle : A ≤ B := by
    exact P.selfAdjoint_le_coordinate_unboundedIntegral_of_cayley
      A hA cayleyCoordinate cayleyCoordinate_measurable
      cayleyCoordinate_bounded cayleyCoordinate_relation hphase
  have hsym : B.IsFormalAdjoint B :=
    P.coordinate_unboundedIntegral_isFormalAdjoint
  exact eq_of_selfAdjoint_le_formalSelfAdjoint A B hA hle hsym
