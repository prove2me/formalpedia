-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_ruin_paymentTimes_clock_iUnion
-- name    : AvramDividend.Classical.avram_wave7_19_ruin_paymentTimes_clock_iUnion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:37:55.662938+00:00
-- url     : https://prove2.me/theorems/cfd0e11a-2de9-4738-abf6-1bf0af8f1d26
-- title:
--   Original ruin-payment time domain is the increasing union of finite integer clocks
-- statement:
--   Exact pathwise exhaustion of the genuine source pre-ruin payment domain (including time zero) by deterministic integer clocks, with no payment at positive ruin time. This is the set-theoretic boundary identity for the W7-08 finite-horizon UBV limit passage. No continuity, creeping, integrability or adaptedness assumption is imposed.
-- source:
--   Source-specific paymentTimes and ruinTime definitions from original DividendStrategy; parent W7-08 source Ito target 6004b387 and finite-clock budget 3c9532b7. Finite-clock exhaustion preserves strict before-ruin semantics.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_ruin_paymentTimes_clock_iUnion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ) :
    paymentTimes (ruinTime X x D ω) ∩ Iic T =
      ⋃ n : ℕ, paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T := by sorry
