-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin_source13_original_annulus_count_card_sub
-- name    : AvramDividend.Classical.avram_mix_fin_source13_original_annulus_count_card_sub
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:31:22.81224+00:00
-- url     : https://prove2.me/theorems/c2935d03-7777-4e53-aaf5-972752728d60
-- title:
--   Original negative annulus count as difference of finite cutoff cardinalities
-- statement:
--   On every original Levy process path, the negative annulus marked jump count is exactly the natural cardinal difference of the two nested full-cutoff finite jump-time sets. This provides the whole-number real factorial and same-cell domination bridge for original factorial moment target 6ea0212e.
-- source:
--   MIX-FIN-SOURCE13 original pathwise factorial diagonal count interface

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_nested_cutoff_annulus_count_additive
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_negative_band_factorial_pair_identity
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin_source13_original_annulus_count_card_sub
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) (ω : Ω) :
    let c : ℝ := -(1 / ((n : ℝ) + 1))
    let d : ℝ := -(1 / ((m : ℝ) + 1))
    let k : ℕ → ℕ := fun i =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T i).toFinset.card
    let J : Set ℝ → ℝ≥0∞ := fun B =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    J (Ioc c d) = ((k m - k n : ℕ) : ℝ≥0∞) := by sorry
