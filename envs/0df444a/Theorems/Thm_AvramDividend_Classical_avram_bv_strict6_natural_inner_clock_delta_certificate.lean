-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_natural_inner_clock_delta_certificate
-- name    : AvramDividend.Classical.avram_bv_strict6_natural_inner_clock_delta_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:27:25.816203+00:00
-- url     : https://prove2.me/theorems/57613c31-f781-462e-90b0-9fa7e1b6ac76
-- title:
--   Exact deterministic strict-horizon clocks T-T/(n+2) approach T monotonically
-- statement:
--   For each positive original BV horizon T, the exact delta_n = T/(n+2) used by the physical stopped-cell witness is positive, at most T, antitone, and tends to zero. This supplies the exact clock hypotheses needed by the Proved strict cash prefix and Fatou bridges without replacing the original fixed delta sequence by an arbitrary cofinal one.

import Mathlib
open Filter Set
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict6_natural_inner_clock_delta_certificate
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    (∀ n, 0 < δ n) ∧ (∀ n, δ n ≤ T) ∧
      Antitone δ ∧ Tendsto δ atTop (𝓝 0) := by sorry
