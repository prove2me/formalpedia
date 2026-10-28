-- Prove2me | Theorems.Thm_AvramDividend_Classical_compactTest_nnreal_uniformBound_finiteLintegral
-- name    : AvramDividend.Classical.compactTest_nnreal_uniformBound_finiteLintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:09:03.149074+00:00
-- url     : https://prove2.me/theorems/e92f0d3f-6854-4649-8790-12e0c9cbe80b
-- title:
--   Uniform finite envelope for compactly supported nonnegative continuous tests
-- statement:
--   Any compactly supported continuous NNReal-valued test function admits the explicit finite uniform bound given by its distance from zero in the bounded-continuous-function space; when the underlying measure has finite mass, this constant bound has finite lower integral.
-- source:
--   Supplies the bound and finite-envelope hypotheses needed to apply the accepted finite-stopping cylinder-reward scalar strong Markov theorem 923863b7-543e-4ddf-8e26-f7249d48d98c to the compact tests defining finite-coordinate path-law uniqueness.

import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.compactTest_nnreal_uniformBound_finiteLintegral
    {Ω Y : Type*} [MeasurableSpace Ω] [TopologicalSpace Y]
    (P : Measure Ω) (hP : P Set.univ ≠ ⊤)
    (f : CompactlySupportedContinuousMap Y ℝ≥0) :
    (∀ y : Y,
      ((f y : ℝ≥0) : ℝ≥0∞) ≤
      ((nndist (0 : BoundedContinuousFunction Y ℝ≥0)
        f.toBoundedContinuousFunction : ℝ≥0) : ℝ≥0∞)) ∧
    (∫⁻ _ : Ω,
      ((nndist (0 : BoundedContinuousFunction Y ℝ≥0)
        f.toBoundedContinuousFunction : ℝ≥0) : ℝ≥0∞) ∂P) ≠ ⊤ := by
  sorry
