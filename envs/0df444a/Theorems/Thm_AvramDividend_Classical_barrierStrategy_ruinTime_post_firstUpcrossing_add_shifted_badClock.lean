-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_ruinTime_post_firstUpcrossing_add_shifted_badClock
-- name    : AvramDividend.Classical.barrierStrategy_ruinTime_post_firstUpcrossing_add_shifted_badClock
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:25:18.797462+00:00
-- url     : https://prove2.me/theorems/609e34dd-069c-4161-83cc-0be858498d0e
-- title:
--   Controlled dividend ruin clock equals first barrier upcrossing plus the shifted reflected ruin clock
-- statement:
--   On a path with a finite first upward passage u that strictly precedes controlled ruin, the original controlled barrier ruin clock equals u plus the infimum of future times at which the shifted Lévy reserve a+X(u+t)-X(u), net of the post-upcrossing reflected dividend regulator max(0,sup_{r≤t}X(u+r)-X(u)), becomes negative. Before u, the original controlled reserve is nonnegative by successful survival; after u, the Proved exact shifted controlled-risk identity gives the event predicate. The pure firstBadClock_shift_of_no_early_breach lemma then transfers the infimum. This is the missing rigorous time-window restart step required by the standing-only barrier valuation theorem.
-- source:
--   Proved shifted post-firstUpcrossing riskProcess criterion a7a95fd9, levyPath_bddAbove_Icc c2066587, and firstBadClock_shift_of_no_early_breach 23721444 when accepted; next input to 79978d61.

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_firstBadClock_shift_of_no_early_breach
import Theorems.Thm_AvramDividend_Classical_riskProcess_post_firstUpcrossing_ruin_iff
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_ruinTime_post_firstUpcrossing_add_shifted_badClock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hsuccess : (u : ℝ≥0∞) <
      ruinTime X x (barrierStrategy X x a) ω) :
    ruinTime X x (barrierStrategy X x a) ω =
      (u : ℝ≥0∞) +
        (⨅ (t : ℝ≥0)
          (_ : a + (X.X (u + t) ω - X.X u ω) <
            max 0
              (sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
                X.X u ω)), (t : ℝ≥0∞)) := by sorry
