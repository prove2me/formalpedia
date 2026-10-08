-- Prove2me | Theorems.Thm_ErschlerZheng_orbitKernel_muBeta_le_and_tail_le_of_three_le
-- name    : ErschlerZheng.orbitKernel_muBeta_le_and_tail_le_of_three_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:16:21.00626+00:00
-- url     : https://prove2.me/theorems/7e86a491-2d92-432a-a4c0-bea1f7634a17
-- title:
--   Proposition 7.18 at distance ⩾ 3 and for r ⩾ 3 — the bounds on P_{μ_β}(x, y), its tail and its truncated second moment hold from d = 3 and r = 3 on
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $1 - \frac1D < \beta < 1$, and let $A$ be a positive integer divisible by $D$. Let $P$ be the transition kernel induced by $\mu_\beta$ (`muBeta`) with $k_n = A\lfloor\log_2 n\rfloor$ (`kLog A`) on the orbit $1^\infty \cdot G_\omega$ (`orbitKernel … oneRay`), and write $d(x, y)$ for the Schreier distance (`orbitDist`). Then there is a constant $C$ such that:
--
--   1. for all $x, y$ in the orbit with $d(x, y) \ge 3$,
--   $$P(x, y) \le C\, d(x,y)^{-1-\beta} (\log_2 d(x,y))^{2A(1-\frac1D+\beta)} (\log_2\log_2 d(x,y))^{1+\frac1D};$$
--   2. for every $x$ in the orbit and every real $r \ge 3$,
--   $$\sum_{y : d(x,y) \ge r} P(x, y) \le C r^{-\beta} (\log_2 r)^{2A(\beta-\frac1D)} (\log_2\log_2 r)^{1+\frac1D},$$
--   $$\sum_{y : d(x,y) \le r} d(x,y)^2 P(x, y) \le C r^{2-\beta} (\log_2 r)^{2A(\beta-\frac1D)} (\log_2\log_2 r)^{1+\frac1D}.$$
--
--   The sums over $y$ are over the orbit, and $\log_2$ is `Real.logb 2`.
--
--   This is not a result of the paper as such: the paper prints Proposition 7.18 with no lower bound on $d_{\mathcal S}(x, y)$ or on $r$, the milestone `ErschlerZheng.orbitKernel_muBeta_le_and_tail_le` asserts the bounds for $d(x, y) \ge 4$ and $r \ge 4$, and this statement extends them to $d(x, y) \ge 3$ and $r \ge 3$. It backs the sentence of the note `orbitKernel_muBeta_le_and_tail_le` “Distance $3$ and $3 \le r < 4$ add nothing, since there the right sides are bounded below by a positive multiple of $C$ while the left sides are at most $16$, so enlarging $C$ covers them.”
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 46, Proposition 7.18, for distances and radii at least 3

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem orbitKernel_muBeta_le_and_tail_le_of_three_le (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (β : ℝ) (hβ1 : 1 - 1 / (D : ℝ) < β) (hβ2 : β < 1) (A : ℕ) (hA : 0 < A)
    (hDA : D ∣ A) :
    ∃ C : ℝ,
      (∀ x y : orbitOne ω, 3 ≤ orbitDist ω x y →
        orbitKernel (grigorchuk ω) (muBeta D ω (kLog A) β) oneRay x y ≤
          C * orbitDist ω x y ^ (-1 - β) *
            Real.logb 2 (orbitDist ω x y) ^ (2 * (A : ℝ) * (1 - 1 / (D : ℝ) + β)) *
            Real.logb 2 (Real.logb 2 (orbitDist ω x y)) ^ (1 + 1 / (D : ℝ))) ∧
      (∀ x : orbitOne ω, ∀ r : ℝ, 3 ≤ r →
        ∑' y : orbitOne ω,
            (if r ≤ orbitDist ω x y then
              orbitKernel (grigorchuk ω) (muBeta D ω (kLog A) β) oneRay x y else 0) ≤
          C * r ^ (-β) * Real.logb 2 r ^ (2 * (A : ℝ) * (β - 1 / (D : ℝ))) *
            Real.logb 2 (Real.logb 2 r) ^ (1 + 1 / (D : ℝ))) ∧
      ∀ x : orbitOne ω, ∀ r : ℝ, 3 ≤ r →
        ∑' y : orbitOne ω,
            (if orbitDist ω x y ≤ r then
              orbitDist ω x y ^ 2 * orbitKernel (grigorchuk ω) (muBeta D ω (kLog A) β) oneRay x y
            else 0) ≤
          C * r ^ (2 - β) * Real.logb 2 r ^ (2 * (A : ℝ) * (β - 1 / (D : ℝ))) *
            Real.logb 2 (Real.logb 2 r) ^ (1 + 1 / (D : ℝ)) := by
  sorry

end ErschlerZheng
