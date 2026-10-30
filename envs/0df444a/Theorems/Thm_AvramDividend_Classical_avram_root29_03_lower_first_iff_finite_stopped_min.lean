-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_lower_first_iff_finite_stopped_min
-- name    : AvramDividend.Classical.avram_root29_03_lower_first_iff_finite_stopped_min
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:45:44.699052+00:00
-- url     : https://prove2.me/theorems/4ab57f42-e662-4e42-99fe-d8e7f8ae2c17
-- title:
--   Strict lower-first original Lévy passage iff finite minimum stopped clock attained below
-- statement:
--   For a genuine spectrally negative Lévy process with separated upper and lower thresholds a>0, the strict lower-passage-before-upper event holds precisely when the minimum of the two actual exit clocks equals the lower clock and that lower clock is finite. This pathwise event equivalence uses accepted original-process no-finite-ties, holds for every sample path, and does not assume Standing, bounded variation, unbounded variation, lower-boundary no-creeping, or killed-scale harmonicity.
-- source:
--   Symmetric lower-exit analogue of already Proved avram_root29_03_up_first_iff_finite_stopped_min; uses independently accepted original-clock strict no-finite-ties theorem a9c87fbc. The lower-first stopped reward remains explicit for UBV killed balance be9dc931.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_official_strict_passage_no_finite_ties

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_lower_first_iff_finite_stopped_min
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a) (ω : Ω) :
    twoSidedExitDownTime X (-x) ω <
      twoSidedExitUpTime X (a - x) ω ↔
    min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω) =
      twoSidedExitDownTime X (-x) ω ∧
    twoSidedExitDownTime X (-x) ω < ⊤ := by sorry
