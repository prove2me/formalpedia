-- Prove2me | Theorems.Thm_ExactDFTRefine_Main_eq_8_9
-- name    : ExactDFTRefine.Main.eq_8_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:01:44.800492+00:00
-- url     : https://prove2.me/theorems/040e2078-9131-4291-b530-9cd8004ddc4d
-- title:
--   §3, Eqs. (8)–(9) — (145/20)^C ≤ E and 20^C T_t = (145/(145/20)^C)(T_t/145^t) ≥ 145L/E
-- statement:
--   With $C$, $t = 1 - C$ and $L$ as in Proposition 3.2 and $E = 251500221699/250000000000$,
--   $$\Big(\frac{145}{20}\Big)^C \le E, \tag{8}$$
--   $$20^C T_t = \frac{145}{(145/20)^C}\cdot\frac{T_t}{145^t} \ge \frac{145L}{E}. \tag{9}$$
--   The scaled target moment $20^C T_t$ is the normalization used by the completion and splitting estimates of Section 4.
--
--   Differences from the source: none.
-- source:
--   Yao, Liu, A Numerical Refinement of an Exact Discrete Fourier Transform Bound, arXiv:2611.01257v1, p. 4, §3, Eqs. (8)–(9)

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments

namespace ExactDFTRefine.Main

/-- **§3, Eqs. (8)–(9)**, p. 4. `(145/20)^C ≤ E` (8), and
`20^C T_t = (145/(145/20)^C) · (T_t/145^t) ≥ 145 L/E` (9), at `t = 1 - C`. -/
theorem eq_8_9 :
    ((145 : ℝ) / 20) ^ Cpar ≤ Ebound ∧
    (20 : ℝ) ^ Cpar * moment tpar targetsT =
      145 / ((145 : ℝ) / 20) ^ Cpar * (moment tpar targetsT / (145 : ℝ) ^ tpar) ∧
    (20 : ℝ) ^ Cpar * moment tpar targetsT ≥ 145 * Lbound / Ebound := by sorry

end ExactDFTRefine.Main
