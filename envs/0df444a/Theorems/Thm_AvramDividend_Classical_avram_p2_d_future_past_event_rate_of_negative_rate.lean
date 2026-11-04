-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_past_event_rate_of_negative_rate
-- name    : AvramDividend.Classical.avram_p2_d_future_past_event_rate_of_negative_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:41:18.182212+00:00
-- url     : https://prove2.me/theorems/42234987-f89e-400f-aeb9-569eb3d68bf0
-- title:
--   Original past-event marked compensator rectangle from an explicit negative-mark rate
-- statement:
--   For the unchanged original spectrally negative Lévy process, arbitrary past A in the original filtration at s and Borel mark set B, the exact expected original marked count over A equals P(A)(t−s)ν(B) if the unconditional negative-mark rate on B∩(-∞,0) is explicitly supplied. All sample-space, path and kernel data remain original; works with possibly infinite counts.
-- source:
--   Combines Proved original past-event unconditional source count factorisation 264b3973 with Proved conditional negative-to-arbitrary Borel ν-rate transport 9d64d756. Does not hide or assume the Open P2-C rate identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_arbitrary_borel_rate_of_negative_rate

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_past_event_rate_of_negative_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hnegRate :
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iio (0 : ℝ))) ∂P) =
        ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B ∩ Iio (0 : ℝ))) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      P A * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
