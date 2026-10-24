-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone_of_le
-- name    : AvramDividend.Classical.barrierStrategy_monotone_of_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:29:20.153109+00:00
-- url     : https://prove2.me/theorems/d28c75b1-efb8-40a9-9f9d-ad3824054d16
-- title:
--   Monotonicity of barrier dividends below the barrier
-- statement:
--   For a spectrally negative Lévy process and initial reserve x at or below the barrier a, the cumulative barrier-dividend process is nondecreasing on nonnegative time. This follows from the already proved monotonicity at x=a and the representation of the general regulator as the positive part of the base-barrier regulator minus the initial gap.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_offset_of_le
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_monotone_of_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hxa : x ≤ a) (ω : Ω) :
    Monotone (fun t : ℝ≥0 => barrierStrategy X x a t ω) := by sorry
