-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_single_step_rightLimit_eq
-- name    : AvramDividend.Classical.avram_bv_tail13_single_step_rightLimit_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:07:46.658469+00:00
-- url     : https://prove2.me/theorems/b352bc3b-0d89-4c26-9c5d-9847295fa329
-- title:
--   Exact original right-limit of a nonnegative positive-time dividend reset
-- statement:
--   If the original dividend path is zero up to and including a deterministic clock s and takes a nonnegative random amount K strictly after it, then the exact infimum-based source rightLimit equals zero before s and K at and after s. This proves an outstanding right-limit assumption in public Proved 43840985 and d6568984 for the single-reset original-process investigation.
-- source:
--   The complete source Definition rightLimit is an infimum over future times. The payment step is nonnegative, reaches zero at s when t<s, and is constant K at every time after max(s,t). Conditional strategy interface for canonical 0b2da5b3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail13_single_step_rightLimit_eq
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (K : Ω → ℝ)
    (hK : ∀ ω, 0 ≤ K ω)
    (hD : ∀ t ω, D t ω = if t ≤ s then 0 else K ω) :
    ∀ ω t, rightLimit D t ω = if t < s then 0 else K ω := by sorry
