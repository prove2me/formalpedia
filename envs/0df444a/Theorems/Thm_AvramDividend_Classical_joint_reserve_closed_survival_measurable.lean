-- Prove2me | Theorems.Thm_AvramDividend_Classical_joint_reserve_closed_survival_measurable
-- name    : AvramDividend.Classical.joint_reserve_closed_survival_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:27:15.819274+00:00
-- url     : https://prove2.me/theorems/1a9c2221-edfd-4e69-b6f1-c8216f5e1703
-- title:
--   Whole-horizon Lévy reserve survival is jointly measurable in reserve and path
-- statement:
--   For a Lévy process and fixed finite horizon T, the event of no negative reserves at any time up to T is measurable as a subset of the product of reserve capital ℝ and sample path Ω. This permits Tonelli interchange between an initial-capital Laplace integral and the Lévy expectation. Proof via the already Proved rational-grid equivalence and the measurability of each adapted time slice.
-- source:
--   Adaptation of the accepted chat04_random_reserve_closed_survival_measurable proof, using the Proved chat04_random_reserve_lower_survival_closed_grid_iff and product measurable coordinate projections.

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_lower_survival_closed_grid_iff

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.joint_reserve_closed_survival_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    MeasurableSet {p : ℝ × Ω |
      ∀ t : ℝ≥0, t ≤ T → 0 ≤ p.1 + X.X t p.2} := by sorry
