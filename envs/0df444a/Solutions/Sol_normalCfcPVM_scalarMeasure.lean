-- Prove2me | solution 1 for normalCfcPVM_scalarMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:02:59.932118+00:00
-- url     : https://prove2.me/submissions/e7bf1909-1c42-45e2-8ae6-573cf7fde356

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

set_option autoImplicit false
open MeasureTheory
open CompactlySupported
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (g : spectrum ℂ U → ℝ) (hg : Measurable g) (x : E) :
    (normalCfcPVM U hU g hg).scalarMeasure x =
      Measure.map g (normalCfcScalarMeasure U hU x) := by
  apply Measure.ext
  intro S hS
  rw [PVM.scalarMeasure_apply _ x S hS, Measure.map_apply hg hS]
  change ENNReal.ofReal
      ((@inner ℂ E _ (normalCfcOperator U hU (g ⁻¹' S) x) x).re) =
    normalCfcScalarMeasure U hU x (g ⁻¹' S)
  rw [inner_normalCfcOperator_self, Complex.ofReal_re, ofReal_measureReal]
