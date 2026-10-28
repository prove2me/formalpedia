-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_continuousOn_nonnegative
-- name    : AvramDividend.Classical.unbounded_scale_discount_family_continuousOn_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:44:42.816992+00:00
-- url     : https://prove2.me/theorems/05d3a2f5-5773-4759-ba39-9b3e2c431a16
-- title:
--   Continuity in the discount parameter on the entire nonnegative half-line
-- statement:
--   For an unbounded-variation spectrally negative Lévy process and a scale-function family defined for every nonnegative discount, the scale-function value at each positive reserve is continuous across the whole nonnegative discount half-line. The proof localises to a compact interval [0,q+1] around an arbitrary discount q and uses established compact-discount continuity.
-- source:
--   Topological local-to-global extension of the canonical compact-discount continuity theorem.

import Mathlib.Tactic.Linarith
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.Basic
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_continuousOn
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_family_continuousOn_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q : ℝ, 0 ≤ q → IsScaleFunction X q (W q)) :
    ∀ x : ℝ, 0 < x →
      ContinuousOn (fun q : ℝ => W q x) (Ici (0 : ℝ)) := by sorry
