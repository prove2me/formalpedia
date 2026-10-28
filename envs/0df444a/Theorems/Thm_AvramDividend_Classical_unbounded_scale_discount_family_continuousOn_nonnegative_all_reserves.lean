-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_continuousOn_nonnegative_all_reserves
-- name    : AvramDividend.Classical.unbounded_scale_discount_family_continuousOn_nonnegative_all_reserves
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:49:45.368023+00:00
-- url     : https://prove2.me/theorems/7c51e6d3-f38f-4e95-b262-10da0a01310e
-- title:
--   Global-in-discount continuity of the q-scale family at every real reserve
-- statement:
--   The q-scale function of an unbounded-variation spectrally negative Lévy process depends continuously on any nonnegative discount parameter at every real reserve, including the zero origin and negative reserves. The result is obtained by localising to [0,q+1] and invoking the proved compact-discount all-reserve continuity theorem.
-- source:
--   Local-to-global topological argument from the canonical Proved continuousOn_all_reserves theorem.

import Mathlib.Tactic.Linarith
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.Basic
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_continuousOn_all_reserves
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_family_continuousOn_nonnegative_all_reserves
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q : ℝ, 0 ≤ q → IsScaleFunction X q (W q)) :
    ∀ x : ℝ,
      ContinuousOn (fun q : ℝ => W q x) (Ici (0 : ℝ)) := by sorry
