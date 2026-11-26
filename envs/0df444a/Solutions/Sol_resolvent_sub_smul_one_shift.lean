-- Prove2me | solution 1 for resolvent_sub_smul_one_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:53:33.832672+00:00
-- url     : https://prove2.me/submissions/ffef8f99-1be6-4257-923e-162ceb45b734

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sets.Compacts
import Definitions.Def_Operator_Crouzeix_CircleCauchy

set_option autoImplicit false
open Complex Set spectrum TopologicalSpace
open scoped Real Interval
universe u
variable {B : Type u} [NormedRing B] [NormedAlgebra ℂ B]
variable [CompleteSpace B]
variable [NormOneClass B]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
omit [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) (c z : ℂ) :
    resolvent (A - c • (1 : E →L[ℂ] E)) z = resolvent A (z + c) := by
  unfold resolvent
  congr 1
  simp only [Algebra.algebraMap_eq_smul_one]
  module
