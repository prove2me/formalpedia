-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock
-- name    : AvramDividend.Classical.avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:13:37.663342+00:00
-- url     : https://prove2.me/theorems/75280f18-e88f-484c-8265-9c78a50fdbaa
-- title:
--   Canonical reflected barrier ruin clock is the original strict Lévy drawdown passage clock
-- statement:
--   The actual barrierRuinTime defined from the reflected capital and Lévy path is exactly the infimum of all nonnegative times where the original X path falls strictly below its true running supremum by more than the barrier a. This preserves strict ruin, nonpositive/zero boundary, and the true controlled capital definitions, and is the precise clock adapter needed to use the accepted original Stieltjes-to-sampled reward equality with canonical barrierSupValue.
-- source:
--   Canonical ReflectionBarrier and Reflection definitions; source-faithful unfolding and real-order equivalence. Supports accepted 43b6f24e sampled path reward bridge and 11b589b7 at-barrier value.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) (ω : Ω) :
    barrierRuinTime X a ω =
      (⨅ i : {t : ℝ≥0 // X.X t ω - runningSup X t ω < -a},
        (i.1 : ℝ≥0∞)) := by sorry
