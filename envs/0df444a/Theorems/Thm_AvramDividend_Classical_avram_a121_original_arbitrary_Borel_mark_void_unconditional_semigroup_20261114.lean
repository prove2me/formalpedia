-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a121_original_arbitrary_Borel_mark_void_unconditional_semigroup_20261114
-- name    : AvramDividend.Classical.avram_a121_original_arbitrary_Borel_mark_void_unconditional_semigroup_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:28:38.063974+00:00
-- url     : https://prove2.me/theorems/035d82b6-0e2d-4b2d-ab7c-e9254fe52fbb
-- title:
--   Original arbitrary Borel marked-jump void probabilities form an unconditional multiplicative time semigroup
-- statement:
--   For every original spectrally negative Lévy process, every Borel mark set B, and every two nonnegative horizons s,T, the probability of no physical B-marked jump during (0,s+T] equals the product of probabilities on (0,s] and (0,T]. Raw adaptedness of the original physical Borel count, pathwise adjacent-horizon splitting, exact original past/future event independence and stationarity are all already proved, so no extra measurability premise is needed.
-- source:
--   Proved original arbitrary Borel count raw F_s measurability A20, Proved A118 marked void pathwise split, Proved wave7_06 arbitrary Borel future void/past factor, Proved arbitrary Borel shifted void stationarity c64a7b2a; direct strengthening of A119.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a121_original_arbitrary_Borel_mark_void_unconditional_semigroup_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) :
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (s + T) ×ˢ B) = 0} =
      P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 s ×ˢ B) = 0} *
      P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B) = 0} := by sorry
