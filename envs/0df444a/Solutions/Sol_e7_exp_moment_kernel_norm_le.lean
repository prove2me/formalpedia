-- Prove2me | solution 1 for e7_exp_moment_kernel_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:38:54.415211+00:00
-- url     : https://prove2.me/submissions/9106350c-25d7-41de-86e0-28aeeba712f4

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
import Definitions.Def_e7_exp_moment_kernel
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
open EthierKurtz Classical

theorem e7_exp_moment_kernel_norm_le
    (d : ℝ → ℝ) (k : ℕ) (B : ℝ)
    (hd_bound : ∀ r : ℝ, ‖d r‖ ≤ B)
    {y : ℝ} (hy : y ∈ Set.Ioc (0 : ℝ) 1) :
    ‖e7_exp_moment_kernel d k y‖ ≤ B := by
  unfold e7_exp_moment_kernel
  rw [if_pos (show 0 < y ∧ y ≤ 1 from hy), norm_mul, norm_pow]
  have h1 : ‖y‖ ^ k ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (by rw [Real.norm_eq_abs, abs_of_pos hy.1]; exact hy.2)
  calc ‖y‖ ^ k * ‖d (-Real.log y)‖ ≤ 1 * B :=
        mul_le_mul h1 (hd_bound _) (norm_nonneg _) zero_le_one
    _ = B := one_mul B

theorem solution
    (d : ℝ → ℝ) (k : ℕ) (B : ℝ)
    (hd_bound : ∀ r : ℝ, ‖d r‖ ≤ B)
    {y : ℝ} (hy : y ∈ Set.Ioc (0 : ℝ) 1) :
    ‖e7_exp_moment_kernel d k y‖ ≤ B := by
  unfold e7_exp_moment_kernel
  rw [if_pos (show 0 < y ∧ y ≤ 1 from hy), norm_mul, norm_pow]
  have h1 : ‖y‖ ^ k ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (by rw [Real.norm_eq_abs, abs_of_pos hy.1]; exact hy.2)
  calc ‖y‖ ^ k * ‖d (-Real.log y)‖ ≤ 1 * B :=
        mul_le_mul h1 (hd_bound _) (norm_nonneg _) zero_le_one
    _ = B := one_mul B


