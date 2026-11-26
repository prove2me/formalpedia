-- Prove2me | solution 1 for mderiv_closable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:09:13.933608+00:00
-- url     : https://prove2.me/submissions/0ab61422-6ffe-413b-b88b-bf0ca4dae1d3

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
    (F : ℕ → {F : W → ℝ // IsSmoothBounded F})
    {η : Lp (CameronMartin.Space μ) 2 μ}
    (hF : Tendsto (fun k ↦ (F k).2.toLp μ) atTop (𝓝 0))
    (hD : Tendsto (fun k ↦ (F k).2.mderivLp μ) atTop (𝓝 η)) :
    η = 0 :=
  Malliavin.mderiv_closable μ
    (fun k ↦ ⟨(F k).1, Malliavin.IsSmoothBounded.mk
      (F k).2.contDiff (F k).2.bounded (F k).2.bounded_fderiv⟩)
    hF hD
