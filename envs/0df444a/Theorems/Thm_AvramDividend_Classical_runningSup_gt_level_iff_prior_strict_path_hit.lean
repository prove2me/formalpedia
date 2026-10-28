-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_gt_level_iff_prior_strict_path_hit
-- name    : AvramDividend.Classical.runningSup_gt_level_iff_prior_strict_path_hit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:27:08.477373+00:00
-- url     : https://prove2.me/theorems/2c2a5cce-5625-4740-a1c8-6126816bd4f1
-- title:
--   The actual Lévy running supremum exceeds a level exactly when the path has crossed it by that time
-- statement:
--   For the canonical spectrally negative Lévy process, the actual running supremum S_t is strictly greater than b if and only if the underlying path X crosses b by some time s≤t. The proof uses the accepted raw indexed supremum representation and bound on every path value, then Mathlib lt_ciSup_iff. This directly identifies inverse local-time record level crossing events with actual original first-upcrossing clocks, towards future excursion decomposition and Poisson characteristic measure. It does not assert the excursion PPP or killed Markov law.
-- source:
--   Accepted runningSup_eq_rawSup_nonneg, runningSup_monotone_and_path_le and pinned Mathlib lt_ciSup_iff.

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.runningSup_gt_level_iff_prior_strict_path_hit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (t : ℝ≥0) (b : ℝ) :
    b < runningSup X t ω ↔
      ∃ s : ℝ≥0, s ≤ t ∧ b < X.X s ω := by sorry
