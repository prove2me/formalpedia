-- Prove2me | solution 1 for levy_foundations_posDefPointwiseLimit
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:09:56.777688+00:00
-- url     : https://prove2.me/submissions/936d1e0c-2618-426e-a0c5-6e0554420047

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_levy_foundations_isPositiveDefinite

open MeasureTheory Complex ComplexConjugate Finset Filter Topology Matrix
open scoped NNReal ENNReal ComplexOrder

theorem solution
    {φs : ℕ → ℝ → ℂ}
    (hφs : ∀ n, LevyFoundations.isPositiveDefinite (φs n))
    {φ : ℝ → ℂ} (hlim : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x))) :
    LevyFoundations.isPositiveDefinite φ := by
  intro n x c
  have hT : Tendsto (fun k => ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * φs k (x i - x j)) atTop
      (𝓝 (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * φ (x i - x j))) := by
    refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_
    exact (hlim (x i - x j)).const_mul _
  exact ge_of_tendsto' hT fun k => hφs k n x c
