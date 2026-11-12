-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja19_original_smallband_finsum_card_le_total_count
-- name    : AvramDividend.Classical.avram_ja19_original_smallband_finsum_card_le_total_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:16:03.368317+00:00
-- url     : https://prove2.me/theorems/93121b6f-e8b5-4e31-b9f0-26cd7ba5fff6
-- title:
--   Original finite band marked index cardinality bounded by total negative jump count
-- statement:
--   For each original same-space sample path with finite total negative jump count on (0,T], the finite set of times whose jumps lie in (-1,-1/(k+1)] before t≤T has cardinality at most the total marked Poisson jump count. Requires the injective time-to-mark map and count measure on the original probability space; avoid all auxiliary processes and large-mark first moments.
-- source:
--   J-A19 original count/card bridge

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja19_original_smallband_finsum_card_le_total_count
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ T : ℝ≥0,
      let N : Ω → ℝ≥0∞ := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iio (0 : ℝ))
      ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t : ℝ≥0, t ≤ T →
        ∃ F : Finset ℝ≥0,
          (∀ u : ℝ≥0, u ∈ F ↔
             0 < u ∧ u ≤ t ∧
             -1 < X.X u ω -
               Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
             X.X u ω -
               Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
               -(1 / ((k : ℝ) + 1))) ∧
          (F.card : ℝ) ≤ (N ω).toReal := by sorry
