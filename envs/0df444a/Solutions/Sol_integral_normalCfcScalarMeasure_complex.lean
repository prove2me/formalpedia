-- Prove2me | solution 1 for integral_normalCfcScalarMeasure_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:03:10.818094+00:00
-- url     : https://prove2.me/submissions/31c3c5d0-4e89-486f-8e53-aa2296c0cf5b

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
section
open MeasureTheory
open CompactlySupported
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem cfc_inner_self_real_of_real_valued
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (f : C(spectrum ℂ U, ℂ)) (hreal : star f = f) (x : E) :
    ((@inner ℂ E _ x ((cfcHom hU) f x)).re : ℂ) =
      @inner ℂ E _ x ((cfcHom hU) f x) := by
  have hself : IsSelfAdjoint ((cfcHom hU) f) := by
    change star ((cfcHom hU) f) = (cfcHom hU) f
    rw [← map_star, hreal]
  exact hself.isSymmetric.coe_re_inner_self_apply x
end

set_option autoImplicit false
open MeasureTheory
open CompactlySupported
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E)
    (f : C(spectrum ℂ U, ℂ)) :
    ∫ z, f z ∂(normalCfcScalarMeasure U hU x) =
      @inner ℂ E _ x ((cfcHom hU) f x) := by
  let fr : C_c(spectrum ℂ U, ℝ) := continuousMapRealPart f
  let fi : C_c(spectrum ℂ U, ℝ) := continuousMapImagPart f
  let fre : C(spectrum ℂ U, ℂ) := continuousMapOfRealPart f
  let fim : C(spectrum ℂ U, ℂ) := continuousMapOfImagPart f
  have hr := integral_normalCfcScalarMeasure U hU x fr
  have hi := integral_normalCfcScalarMeasure U hU x fi
  change (∫ z, (f z).re ∂(normalCfcScalarMeasure U hU x)) =
      (@inner ℂ E _ x ((cfcHom hU) fre x)).re at hr
  change (∫ z, (f z).im ∂(normalCfcScalarMeasure U hU x)) =
      (@inner ℂ E _ x ((cfcHom hU) fim x)).re at hi
  have hfre : star fre = fre := by
    ext z
    change star ((f z).re : ℂ) = ((f z).re : ℂ)
    rw [Complex.star_def, Complex.conj_ofReal]
  have hfim : star fim = fim := by
    ext z
    change star ((f z).im : ℂ) = ((f z).im : ℂ)
    rw [Complex.star_def, Complex.conj_ofReal]
  have hdecomp : f = fre + Complex.I • fim := by
    ext z
    change f z = ((f z).re : ℂ) + Complex.I * ((f z).im : ℂ)
    rw [mul_comm]
    exact (Complex.re_add_im (f z)).symm
  have hfint : Integrable f (normalCfcScalarMeasure U hU x) := by
    apply Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
    exact ae_of_all _ fun z => f.norm_coe_le_norm z
  rw [← integral_re_add_im hfint]
  change (((∫ z, (f z).re ∂(normalCfcScalarMeasure U hU x)) : ℝ) : ℂ) +
      (((∫ z, (f z).im ∂(normalCfcScalarMeasure U hU x)) : ℝ) : ℂ) *
        Complex.I = @inner ℂ E _ x ((cfcHom hU) f x)
  rw [hr, hi]
  rw [hdecomp, map_add, map_smul, add_apply, smul_apply,
    inner_add_right, inner_smul_right]
  rw [cfc_inner_self_real_of_real_valued U hU fre hfre x,
    cfc_inner_self_real_of_real_valued U hU fim hfim x]
  ring
