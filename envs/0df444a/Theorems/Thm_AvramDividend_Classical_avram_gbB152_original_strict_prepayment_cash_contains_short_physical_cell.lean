-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB152_original_strict_prepayment_cash_contains_short_physical_cell
-- name    : AvramDividend.Classical.avram_gbB152_original_strict_prepayment_cash_contains_short_physical_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:08:57.563911+00:00
-- url     : https://prove2.me/theorems/517fe8f5-eaf1-4ef5-beb7-f60c4d4b0323
-- title:
--   Every short physical Ioc cash cell strictly before ruin belongs to original strictly prior payment times
-- statement:
--   If S is strictly earlier than both a physical stopping horizon T and the original extended-nonnegative ruin time σ, then the entire physical interval (0,S] is contained in the original paymentTimes σ and strictly before T. This exact source set-inclusion lemma permits lower bounds on original stopped strict Stieltjes cash by restricting to an interior finite physical cell.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB152_original_strict_prepayment_cash_contains_short_physical_cell
    (σ : ℝ≥0∞) (S T : ℝ≥0)
    (hS : (S : ℝ≥0∞) < σ)
    (hST : S < T) :
    Ioc (0 : ℝ) (S : ℝ) ⊆
      paymentTimes σ ∩ Iio (T : ℝ) := by sorry
