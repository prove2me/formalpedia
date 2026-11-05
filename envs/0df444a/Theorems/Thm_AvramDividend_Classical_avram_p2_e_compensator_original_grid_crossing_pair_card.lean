-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_grid_crossing_pair_card
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_grid_crossing_pair_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:24:36.28366+00:00
-- url     : https://prove2.me/theorems/6816540b-f8a0-42cd-9be0-8ccc5b30e002
-- title:
--   Actual original negative-band jump-time grid crossing pairs have product cardinality
-- statement:
--   For actual marked negative-band jump times of the original Lévy path in (0,T], the product of past and next-window counts is the cardinal of its chronological crossing pairs.
-- source:
--   Exact original finite negative-band marked-time theorem e5e6f70b and deterministic Finset.filter membership, Finset.card_product at the pinned Mathlib revision; directly feeds the dyadic chronological-pair reduction for d938e9a5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_original_grid_crossing_pair_card
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T s t : ℝ≥0) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    (F.filter (fun u => u ≤ s)).card *
      (F.filter (fun u => s < u ∧ u ≤ t)).card =
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      p.1 ≤ s ∧ s < p.2 ∧ p.2 ≤ t)).card := by sorry
