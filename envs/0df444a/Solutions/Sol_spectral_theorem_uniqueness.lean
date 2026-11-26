-- Prove2me | solution 1 for spectral_theorem_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:13:07.403842+00:00
-- url     : https://prove2.me/submissions/15a9d6f9-a741-46e6-be62-ffa282978b06

import Definitions.Def_Spectral_Stone_Theorem
import Definitions.Def_Spectral_Spectral_FuncCalc
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Definitions.Def_Spectral_Spectral_Uniqueness
import Theorems.Thm_spectral_theorem_uniqueness_on_measurable

set_option autoImplicit false
open Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (E₁ E₂ : PVM E)
    (h₁ : E₁.unboundedIntegral ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable = A)
    (h₂ : E₂.unboundedIntegral ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable = A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    E₁.proj S = E₂.proj S :=
  spectral_theorem_uniqueness_on_measurable A hA E₁ E₂ h₁ h₂ S hS
