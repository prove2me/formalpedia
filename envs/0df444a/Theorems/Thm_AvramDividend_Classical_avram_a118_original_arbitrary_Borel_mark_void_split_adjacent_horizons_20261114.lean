-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a118_original_arbitrary_Borel_mark_void_split_adjacent_horizons_20261114
-- name    : AvramDividend.Classical.avram_a118_original_arbitrary_Borel_mark_void_split_adjacent_horizons_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:22:59.811201+00:00
-- url     : https://prove2.me/theorems/fbb08a2b-3f93-48c8-9744-6524eeefd1f5
-- title:
--   Original physical marked-jump void event splits exactly across adjacent time intervals for every Borel mark set
-- statement:
--   On every path of the original spectrally negative Lévy process, the count of actual Borel marked jumps on (0,T+S] is zero exactly when both counts on (0,T] and (T,T+S] are zero. The result is pure count-measure geometry for any set of marks B, independent of activity, Gaussian volatility, and probability law.
-- source:
--   Existing Proved wave7_06_original_intrinsic_negative_band_void_split_adjacent_horizons; generalise its identical measure-union argument from negative cut-off band to arbitrary B.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a118_original_arbitrary_Borel_mark_void_split_adjacent_horizons_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T S : ℝ≥0) (B : Set ℝ) :
    (let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     NX (Ioc 0 (T + S) ×ˢ B) = 0 ↔
       NX (Ioc 0 T ×ˢ B) = 0 ∧
       NX (Ioc T (T + S) ×ˢ B) = 0) := by sorry
