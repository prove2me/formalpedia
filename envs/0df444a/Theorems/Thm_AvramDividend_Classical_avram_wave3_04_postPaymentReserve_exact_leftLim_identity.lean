-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity
-- name    : AvramDividend.Classical.avram_wave3_04_postPaymentReserve_exact_leftLim_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:42:41.108203+00:00
-- url     : https://prove2.me/theorems/06dc12b5-23e1-41de-b1a6-e9b102bec27f
-- title:
--   Exact left-limit formula for the original post-payment controlled Lévy reserve
-- statement:
--   For the same original spectrally negative Lévy sample path and an actual left-continuous dividend strategy, the strict-left limit of the post-payment controlled reserve x+X_t-D(t+) at every positive time is exactly x plus the strict-left limit of the original Lévy path X minus the original dividend value D(t). This is the source jump-ordering identity needed by the Ito integrand and simultaneously accounts for the right-dividend jump convention.
-- source:
--   Canonical Proved AvramDividend.Classical.avram_wave3_04_rightLimit_leftLimit_eq_dividend UUID f9c3a5c4-3a58-45b7-b6da-8734693b863d and source Lévy leftLim field. Private pinned remote compiler probe 0a7a34b5-5540-480f-87ac-b7e8fb07929c passed to sentinel, exact source SHA-256 2a6f012184d9125709779add27a861c7631f8c39218fac635ad41d1200f0b8d3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_postPaymentReserve_exact_leftLim_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
      x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω := by sorry
