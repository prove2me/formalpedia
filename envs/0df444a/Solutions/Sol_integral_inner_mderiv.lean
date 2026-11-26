-- Prove2me | solution 1 for integral_inner_mderiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:09:11.583135+00:00
-- url     : https://prove2.me/submissions/71806f84-208f-4a7e-be26-cb87a2fc5a8a

import Definitions.Def_Malliavin
import Definitions.Def_Malliavin_Solution

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Real Topology InnerProductSpace
theorem _root_.solution
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (μ : Measure W) [IsGaussian μ]
    {F : W → ℝ} (hF : IsSmoothBounded F) (h : CameronMartin.Space μ) :
    ∫ x, ⟪mderiv μ F x, h⟫_ℝ ∂μ =
      ∫ x, F x * (h : Lp ℝ 2 μ) x ∂μ :=
  Malliavin.integral_inner_mderiv μ
    (Malliavin.IsSmoothBounded.mk
      hF.contDiff hF.bounded hF.bounded_fderiv)
    h
