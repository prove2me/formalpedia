-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja19_original_smallband_negative_finsum_card_le_total_count
-- name    : AvramDividend.Classical.avram_ja19_original_smallband_negative_finsum_card_le_total_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:58:44.861522+00:00
-- url     : https://prove2.me/theorems/216c33ad-7191-416b-99f8-401ef6dddf6c
-- title:
--   Original negative small-band marked finite sum bounded by total jump count
-- statement:
--   Under finite negative activity, outside the null set with infinite total negative jump count, each finite set of marked original jumps in (-1,-1/(k+1)] before t≤T injects into the total negative-jump count on (0,T]. Every included mark has magnitude at most one, so the absolute finite sum is at most the total jump count. Match the marked process count to finite cardinality using original source Proved 1c1d4731 and a6562a4d. No assumption on the magnitude of large negative jumps.
-- source:
--   J-A19 original physical marked count comparison

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja19_original_smallband_negative_finsum_card_le_total_count
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
          |∑ u ∈ F,
             (X.X u ω -
                Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)| ≤
            (N ω).toReal := by sorry
