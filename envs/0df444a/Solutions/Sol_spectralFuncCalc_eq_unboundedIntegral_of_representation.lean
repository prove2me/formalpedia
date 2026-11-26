-- Prove2me | solution 1 for spectralFuncCalc_eq_unboundedIntegral_of_representation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:13:57.014833+00:00
-- url     : https://prove2.me/submissions/127644c0-6296-46f2-a7a2-9ef74561d0ad

import Definitions.Def_Spectral_Stone_Theorem
import Definitions.Def_Spectral_Spectral_FuncCalc
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Definitions.Def_Spectral_Spectral_Uniqueness
import Theorems.Thm_spectral_theorem_uniqueness
import Theorems.Thm_PVM_unboundedIntegral_eq_of_proj_eq_on_measurable
import Theorems.Thm_spectral_theorem_existence


set_option autoImplicit false
open Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (E_pvm : PVM E)
    (hE : E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable = A)
    (f : ℝ → ℂ) (hf : Measurable f) :
    spectralFuncCalc A hA f hf = E_pvm.unboundedIntegral f hf := by
  apply PVM.unboundedIntegral_eq_of_proj_eq_on_measurable
  intro S hS
  exact spectral_theorem_uniqueness A hA
    (Classical.choose (spectral_theorem_existence A hA)) E_pvm
    (Classical.choose_spec (spectral_theorem_existence A hA)) hE S hS
