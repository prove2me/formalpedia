-- Prove2me | solution 1 for e7_log_density_clamped_continuous
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:39:01.6453+00:00
-- url     : https://prove2.me/submissions/682388ff-aef7-4b53-890f-21b156e3bd6a

import Definitions.Def_auto_M04_6e37b463_SolvesMartingaleProblem
import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction
import Definitions.Def_auto_M04_6e37b463_processPast
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Definitions.Def_e7_clampIcc
import Definitions.Def_e7_log_density_clamped
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
open EthierKurtz Classical

theorem e7_log_density_clamped_continuous
    (d : ℝ → ℝ) (hd : Continuous d) (a b : ℝ) (hab : a ≤ b) (ha : 0 < a) :
    Continuous (e7_log_density_clamped d a b hab) := by
  unfold e7_log_density_clamped
  exact hd.comp (Continuous.neg (Continuous.log
    (continuous_subtype_val.comp (e7_clampIcc a b hab).continuous)
    (fun y => ne_of_gt (lt_of_lt_of_le ha (e7_clampIcc a b hab y).2.1))))

theorem solution
    (d : ℝ → ℝ) (hd : Continuous d) (a b : ℝ) (hab : a ≤ b) (ha : 0 < a) :
    Continuous (e7_log_density_clamped d a b hab) := by
  unfold e7_log_density_clamped
  exact hd.comp (Continuous.neg (Continuous.log
    (continuous_subtype_val.comp (e7_clampIcc a b hab).continuous)
    (fun y => ne_of_gt (lt_of_lt_of_le ha (e7_clampIcc a b hab y).2.1))))


