-- Prove2me | Theorems.Thm_ExactDFTRefine_Main_eq_11
-- name    : ExactDFTRefine.Main.eq_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:01:50.144229+00:00
-- url     : https://prove2.me/theorems/88c5bbfa-8867-48a0-8adf-e07c7b01716e
-- title:
--   §3, Eq. (11) — P_1/(20^C T_t) ≤ γ and 21|T|/(20^C T_t) ≤ η
-- statement:
--   With $\gamma = 99857/100000$, $\eta = 9583/10000$ (Eq. (10)), $C$, $t = 1-C$, $L$, $E$ as above, the rational inequalities
--   $$239134 \le \gamma\,\frac{145L}{E}, \qquad 10928\cdot 21 \le \eta\,\frac{145L}{E}$$
--   hold, and
--   $$\frac{P_1}{20^C T_t} \le \gamma, \qquad \frac{21|T|}{20^C T_t} \le \eta. \tag{11}$$
--   These two ratios are the bases of the two tail terms of Eq. (14).
--
--   Differences from the source:
--   - reading: the rational inequalities 239134 ≤ γ·145L/E, 10928·21 ≤ η·145L/E and (2) imply (11) → the conjunction of both rational inequalities and both inequalities of (11); reason: the paper asserts the rational inequalities as facts and derives (11) from them; stating all four keeps every claim of the passage
-- source:
--   Yao, Liu, A Numerical Refinement of an Exact Discrete Fourier Transform Bound, arXiv:2611.01257v1, p. 4, §3, Eqs. (10)–(11)

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments

namespace ExactDFTRefine.Main

/-- **§3, Eq. (11)**, p. 4. The rational inequalities `239134 ≤ γ · 145L/E` and
`10928 · 21 ≤ η · 145L/E` hold, and `P_1/(20^C T_t) ≤ γ`, `21|T|/(20^C T_t) ≤ η` (11), at
`t = 1 - C`. -/
theorem eq_11 :
    (239134 : ℝ) ≤ gam * (145 * Lbound / Ebound) ∧
    (10928 : ℝ) * 21 ≤ eta * (145 * Lbound / Ebound) ∧
    moment 1 blocksP / ((20 : ℝ) ^ Cpar * moment tpar targetsT) ≤ gam ∧
    21 * (Multiset.card targetsT : ℝ) / ((20 : ℝ) ^ Cpar * moment tpar targetsT) ≤ eta := by sorry

end ExactDFTRefine.Main
