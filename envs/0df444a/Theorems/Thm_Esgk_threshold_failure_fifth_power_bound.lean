-- Prove2me | Theorems.Thm_Esgk_threshold_failure_fifth_power_bound
-- name    : Esgk.threshold_failure_fifth_power_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:52:24.482979+00:00
-- url     : https://prove2.me/theorems/e94e4c36-c2f2-4ba9-a330-c6c4b9cdaca6
-- title:
--   Threshold failure gives a fifth-power deficiency bound
-- statement:
--   If $N^2 < C^2 d^5$ with $s \ge 1$, $nd \le N 2s$ and $d \le 2s$, then $n^2 < 32 C^2 s^5$. Below-threshold points force large deficiency; the published fractional-power form raised to the fifth power keeps everything in naturals.
-- source:
--   esgk-on3 lean/Esgk/AdditiveExcessArithmetic.lean (Esgk.threshold_failure_fifth_power_bound)

import Mathlib

namespace Esgk

/-- Threshold failure (§16.3, (16.4)): below the `d^(5/2)` threshold,
i.e. `N^2 < C^2 * d^5`, coverage `n * d ≤ N * (2s)` with `d ≤ 2s` forces
`n^2 < 32 * C^2 * s^5` (the `rpow` form `s > n^(2/5)/(2C^(2/5))`
raised to the fifth power). -/
theorem threshold_failure_fifth_power_bound (n s N d C : ℕ) (hs : 1 ≤ s)
    (hcov : n * d ≤ N * (2 * s)) (hN : N ^ 2 < C ^ 2 * d ^ 5)
    (hds : d ≤ 2 * s) : n ^ 2 < 32 * C ^ 2 * s ^ 5  := by sorry

end Esgk
