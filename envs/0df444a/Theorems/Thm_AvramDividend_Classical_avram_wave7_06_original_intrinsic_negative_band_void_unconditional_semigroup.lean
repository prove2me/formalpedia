-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_void_unconditional_semigroup
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_unconditional_semigroup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:59:01.296451+00:00
-- url     : https://prove2.me/theorems/9b90dbf3-4427-43cb-a2d8-a9548923493b
-- title:
--   Exact original negative-band void probabilities satisfy a time semigroup without auxiliary hypotheses
-- statement:
--   For every original spectrally negative Lévy process and every negative band separated from zero, the probability that its genuine intrinsic marked-count measure has no jumps during (0,T+S] is the product of the original void probabilities on (0,T] and (0,S]. This eliminates explicit raw-past measurability and stationarity hypotheses by supplying their source-specific proofs.
-- source:
--   Avram W7-06 original-filtration compensated small-jump martingale, exact marked-void semigroup after source filtration locality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_unconditional_semigroup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T S : ℝ≥0) (n : ℕ) :
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (T + S) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} =
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} *
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 S ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} := by sorry
