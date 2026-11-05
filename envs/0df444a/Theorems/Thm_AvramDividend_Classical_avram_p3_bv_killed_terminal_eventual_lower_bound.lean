-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_killed_terminal_eventual_lower_bound
-- name    : AvramDividend.Classical.avram_p3_bv_killed_terminal_eventual_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:26:25.77223+00:00
-- url     : https://prove2.me/theorems/c5e64c4c-2f63-490f-b3e6-6f9afccfc3cb
-- title:
--   Deterministic strict-survival killed terminal one-sided lower semicontinuity across exact ruin horizons
-- statement:
--   A deterministic abstraction of the exact killed-terminal lower-semicontinuity step. If the live payoff F is nonnegative before ruin at positive times and continuous from the left only on the strict-survival event, then the killed payoff satisfies the one-sided epsilon lower-bound at every positive horizon, including the case when ruin equals that horizon. This result is needed to justify Fatou passage from strictly earlier horizons in the original BV stochastic HJB verification.
-- source:
--   Deterministic consequence of strict killing, positivity and left-filter convergence, formalising the exact-ruin-time branch in the Avram classical dividend verification. No stochastic assumption or original-process replacement.

import Mathlib
open Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_killed_terminal_eventual_lower_bound
    (r : ℝ≥0∞) (F : ℝ≥0 → ℝ) (t : ℝ≥0) (ht : 0 < t)
    (hpos : ∀ s : ℝ≥0, 0 < s → (s : ℝ≥0∞) < r → 0 ≤ F s)
    (hcont : (t : ℝ≥0∞) < r → Tendsto F (𝓝[<] t) (𝓝 (F t)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : ℝ≥0 in 𝓝[<] t,
      (if (t : ℝ≥0∞) < r then F t else 0) - ε <
      (if (s : ℝ≥0∞) < r then F s else 0) := by sorry
