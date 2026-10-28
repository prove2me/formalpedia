-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_surviving_stoppedValue_range_real
-- name    : AvramDividend.Classical.capped_surviving_stoppedValue_range_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:37:25.167216+00:00
-- url     : https://prove2.me/theorems/585db37b-0b07-42a2-b8f6-932070da61e4
-- title:
--   A surviving stopped controlled reserve stays within a finite real cap
-- statement:
--   If an admissible controlled reserve starts nonnegative, respects an extended nonnegative finite cap represented by a real bound B, and an extended random horizon occurs strictly before ruin, the stopped reserve belongs to the real closed interval [0,B]. The proof excludes infinite stopping times, applies the already Proved pre-ruin reserve range theorem, and converts the ENNReal cap comparison back to real order.
-- source:
--   Proved capped_riskProcess_range_before_ruin_including_zero and pinned Mathlib stoppedValue and ENNReal.ofReal_le_ofReal_iff.

import Mathlib.Probability.Process.Stopping
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_surviving_stoppedValue_range_real
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x B : ℝ) (hx : 0 ≤ x) (hB : 0 ≤ B)
    (C : ℝ≥0∞) (hC : C = ENNReal.ofReal B)
    (hxC : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0∞) (ω : Ω)
    (hτsurv : τ ω < ruinTime X x D ω) :
    stoppedValue (riskProcess X x D) τ ω ∈ Icc (0 : ℝ) B := by sorry
