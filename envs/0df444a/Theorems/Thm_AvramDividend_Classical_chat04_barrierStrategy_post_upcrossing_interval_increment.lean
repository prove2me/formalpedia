-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_barrierStrategy_post_upcrossing_interval_increment
-- name    : AvramDividend.Classical.chat04_barrierStrategy_post_upcrossing_interval_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:28:52.041277+00:00
-- url     : https://prove2.me/theorems/af5b973c-666b-467b-ab3f-49d8f8b8d9e2
-- title:
--   Barrier and running-record increments agree on any post-upcrossing interval
-- statement:
--   For a spectrally negative Lévy path whose strict first upward crossing of a−x occurs at u, and for u≤r≤s, the difference in barrier cumulative dividends between r and s equals the difference in the original running supremum on that same interval. The only path boundedness assumption is above-boundedness through s. This extends the proved anchored record-increment identity to all post-stopping-time intervals, providing the interval generator required for a whole-tail Stieltjes-measure equality.
-- source:
--   Corollary of proved chat04_barrierStrategy_post_upcrossing_record_increment UUID 34849d2f-21f6-49df-99fb-c05206a98ba4, using two endpoint rewrites and additive cancellation.

import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_chat04_barrierStrategy_post_upcrossing_record_increment

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_barrierStrategy_post_upcrossing_interval_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω)
    (u r s : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (v : ℝ≥0) (_ : a - x < X.X v ω), (v : ℝ≥0∞)))
    (hur : u ≤ r) (hrs : r ≤ s)
    (hb : BddAbove ((fun v : ℝ≥0 => X.X v ω) '' Set.Icc 0 s)) :
    barrierStrategy X x a s ω - barrierStrategy X x a r ω =
      runningSup X s ω - runningSup X r ω := by sorry
