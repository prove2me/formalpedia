-- Prove2me | Theorems.Thm_ExactDFTRefine_Main_proposition_3_2
-- name    : ExactDFTRefine.Main.proposition_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:01:37.038212+00:00
-- url     : https://prove2.me/theorems/388f7b65-3bea-4c2e-8ad6-5557c22bfe39
-- title:
--   Proposition 3.2 — P_t/145^t ≤ U, T_t/145^t ≥ L, and P_t/T_t ≤ 1 − ε at t = 1 − C
-- statement:
--   Let $C = 60403319/20000000000$, $t = 1 - C$ and $\varepsilon = 27/10^{12}$ (Eq. (3)), and let $P_t = M_t(P)$, $T_t = M_t(T)$ be the $t$-moments of the Table 1 multisets. Then
--   $$\frac{P_t}{145^t} \le U = \frac{1661483013014771}{10^{12}}, \qquad \frac{T_t}{145^t} \ge L = \frac{1661483013061537}{10^{12}}, \qquad \frac{P_t}{T_t} \le 1 - \varepsilon.$$
--   This is the raw moment gap of the circuit at the certificate parameter $C$: the charged-block moment is a factor $1-\varepsilon$ below the target moment.
--
--   Differences from the source: none.
-- source:
--   Yao, Liu, A Numerical Refinement of an Exact Discrete Fourier Transform Bound, arXiv:2611.01257v1, p. 4, Proposition 3.2 (Eqs. (6), (7))

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments

namespace ExactDFTRefine.Main

/-- **Proposition 3.2**, p. 4. At `t = 1 - C`: `P_t/145^t ≤ U` (6), `T_t/145^t ≥ L` (7), and
consequently `P_t/T_t ≤ 1 - ε`. -/
theorem proposition_3_2 :
    moment tpar blocksP / (145 : ℝ) ^ tpar ≤ Ubound ∧
    moment tpar targetsT / (145 : ℝ) ^ tpar ≥ Lbound ∧
    moment tpar blocksP / moment tpar targetsT ≤ 1 - eps := by sorry

end ExactDFTRefine.Main
