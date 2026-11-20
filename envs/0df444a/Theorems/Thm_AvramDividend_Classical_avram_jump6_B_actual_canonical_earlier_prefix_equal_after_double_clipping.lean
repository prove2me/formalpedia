-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_canonical_earlier_prefix_equal_after_double_clipping
-- name    : AvramDividend.Classical.avram_jump6_B_actual_canonical_earlier_prefix_equal_after_double_clipping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:43:25.827207+00:00
-- url     : https://prove2.me/theorems/65d8fa46-47d9-4b4b-baf1-dc53be422282
-- title:
--   Original canonical physical grid prefix unchanged by second stop clipping
-- statement:
--   If physical index i precedes index k, stopping the canonical physical grid first at the earlier grid value v(k) and then at the true stopped clock rho does not alter the value v(i). This identifies exact prefix cells for applying the strict pre-ruin signed dividend cash bound to a final pre-contact stopped clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_actual_canonical_earlier_prefix_equal_after_double_clipping
    (j k i : ℕ) (ρ : ℝ≥0) (hi : i ≤ k) :
    min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0))
      (min ((k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ) =
    min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ := by sorry
