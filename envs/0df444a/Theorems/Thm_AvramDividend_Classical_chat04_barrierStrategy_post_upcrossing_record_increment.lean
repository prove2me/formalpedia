-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_barrierStrategy_post_upcrossing_record_increment
-- name    : AvramDividend.Classical.chat04_barrierStrategy_post_upcrossing_record_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:57:00.839811+00:00
-- url     : https://prove2.me/theorems/34849d2f-21f6-49df-99fb-c05206a98ba4
-- title:
--   Barrier cumulative dividends after first upcrossing equal the later running-record increment
-- statement:
--   At the finite first strict upcrossing of a-x, the spectrally negative Lévy path attains its running maximum at X_u=a-x. The already Proved barrier restart formula equals the additional running record after u. This exact same-clock equality gives the correct original-time interval increments for dividend Stieltjes measures, repairing the erroneous unshifted RHS in the old open dividend-measure shift target.
-- source:
--   Formal consequence of Proved firstUpcrossing_attains_peak, barrierStrategy_after_firstUpcrossing_shift, runningSup_excess_after_peak and runningSup_eq_rawSup_nonneg.

import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_after_firstUpcrossing_shift
import Theorems.Thm_AvramDividend_Classical_runningSup_excess_after_peak
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_barrierStrategy_post_upcrossing_record_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (u t : ℝ≥0) (ω : Ω)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t))) :
    barrierStrategy X x a (u + t) ω =
      runningSup X (u + t) ω - runningSup X u ω := by sorry
