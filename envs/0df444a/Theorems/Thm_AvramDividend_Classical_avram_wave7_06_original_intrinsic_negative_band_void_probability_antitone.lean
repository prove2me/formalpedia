-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_void_probability_antitone
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_probability_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:32:34.261386+00:00
-- url     : https://prove2.me/theorems/61a5b742-3068-4e5b-9adf-0ef7449fd5bc
-- title:
--   Original intrinsic negative-band void probability decreases with the truncation index
-- statement:
--   For the original probability measure P and the intrinsic marked jump measure of the actual X, the probability of zero negative-band jumps in (0,T] decreases as n grows, because the band at or below -1/(n+1) expands. No Poisson law is assumed, and the inequality is for arbitrary P.
-- source:
--   Source-specific monotonicity of truncation void probabilities supporting the original small-jump L²/L¹ limit and Poisson zero-count child 390a8092-89ae-45c8-bed8-b43b900baa2f, mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_probability_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n m : ℕ) (hnm : n ≤ m) :
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     P {ω : Ω | NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((m : ℝ) + 1)))) = 0} ≤
       P {ω : Ω | NX ω (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}) := by sorry
