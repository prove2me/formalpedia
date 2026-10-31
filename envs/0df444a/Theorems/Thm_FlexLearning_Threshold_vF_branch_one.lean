-- Prove2me | Theorems.Thm_FlexLearning_Threshold_vF_branch_one
-- name    : FlexLearning.Threshold.vF_branch_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:04.54199+00:00
-- url     : https://prove2.me/theorems/46dfb638-7abe-43d5-93fb-b4934093cf8e
-- title:
--   Proof of Proposition 1, pp. A6–A7 — flexible case j = 1: v_F concave on [2x+U, 2x+2U], slope at 2x+U, threshold p̃ < 2c_F
-- statement:
--   In the two-period model with second-period demand equal to first-period demand, independent demands uniform on $[x, x+U]$ ($x \ge 0$, $U > 0$), price $p$, dedicated unit cost $c$ and flexible unit cost $c_F$ with $0 < c \le c_F < p$, let $v_F(Q_F)$ be the two-period objective of the flexible system at first-period flexible capacity $Q_F$. Then:
--   1. $v_F$ is concave on $[2x+U,\, 2x+2U]$;
--   2. its right derivative at $2x + U$ is
--   $$\frac{-c^2 + cp + p(p - 2c_F)}{2p};$$
--   3. this slope is nonnegative if and only if $p \ge \tilde p$, where $\tilde p = \tfrac12\big(2c_F - c + \sqrt{5c^2 - 4cc_F + 4c_F^2}\big)$;
--   4. $\tilde p < 2c_F$.
--
--   Case $j = 1$ ($Q_F \ge 2x+U$) is the regime in which product 1's demand is always observed; together with case $j = 3$ it is the only regime at $x = 0$, and it splits the proof of Proposition 1 into sub-cases.
--
--   **Formalization Note** $U > 0$ and $c > 0$ are added ($\tilde p < 2c_F$ fails at $c = 0$, where $\tilde p = 2c_F$). The concavity is stated only on $[2x+U, 2x+2U]$, where the page's second derivative applies. Item 2 is a one-sided derivative within $[2x+U, \infty)$.
-- source:
--   Chod, Markakis & Trichakis, On the Learning Benefits of Resource Flexibility, SSRN preprint 3212177 (version of December 6, 2019), pp. A6–A7 (PDF 39–40), proof of Proposition 1, case j = 1

import Mathlib
import Definitions.Def_FlexLearning_Threshold_Model

namespace FlexLearning.Threshold

theorem vF_branch_one (p c x U cF : ℝ) (hc : 0 < c) (hccF : c ≤ cF) (hcFp : cF < p)
    (hx : 0 ≤ x) (hU : 0 < U) :
    ConcaveOn ℝ (Set.Icc (2 * x + U) (2 * x + 2 * U)) (vF p c x U cF) ∧
    HasDerivWithinAt (vF p c x U cF) ((-c ^ 2 + c * p + p * (p - 2 * cF)) / (2 * p))
      (Set.Ici (2 * x + U)) (2 * x + U) ∧
    (0 ≤ (-c ^ 2 + c * p + p * (p - 2 * cF)) / (2 * p) ↔ pTilde c cF ≤ p) ∧
    pTilde c cF < 2 * cF := by sorry

end FlexLearning.Threshold
