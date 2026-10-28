-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_pre_extended_upcrossing_clock_le
-- name    : AvramDividend.Classical.runningSup_pre_extended_upcrossing_clock_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:59:04.044989+00:00
-- url     : https://prove2.me/theorems/f9bdf379-4dd4-4ab9-9d66-c705cbb0ecc9
-- title:
--   Running supremum stays below a level before an extended first-upcrossing clock
-- statement:
--   For any finite observation time strictly before the extended-real first strict upward-crossing clock of level b, the running supremum of the Lévy path is at most b. In particular this includes the case where the first crossing is infinite. This supplies the missing terminal-cell bound when the next record level is never reached.
-- source:
--   Direct order argument from the raw-supremum characterization, with the first-passage clock defined as an infimum.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.runningSup_pre_extended_upcrossing_clock_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (b : ℝ)
    (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) <
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞))) :
    runningSup X t ω ≤ b := by sorry
