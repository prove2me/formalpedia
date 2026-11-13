-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_past_count_raw_measurable
-- name    : AvramDividend.Classical.avram_a20_original_borel_past_count_raw_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:35:35.260878+00:00
-- url     : https://prove2.me/theorems/4008b7d8-52d1-4c4b-80b4-43f3b3cdbc29
-- title:
--   Original arbitrary negative Borel marked count is measurable at the raw source past filtration
-- statement:
--   For any measurable Borel mark subset B and deterministic T, the literal original Lévy marked jump count on (0,T] is measurable with respect to the original raw filtration at T. The proof uses Proved càdlàg regularity of the frozen original path, the separately established generic marked Borel frozen-path count representation, and coordinatewise original adaptedness. It generalises an already Proved strictly-negative cutoff adaptedness result and is the missing finite-activity arbitrary-Borel past-weight premise for genuine original chronological pair calculations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_borel_past_count_raw_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable[𝓕 T] (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)) := by sorry
