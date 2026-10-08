-- Prove2me | Theorems.Thm_ErschlerZheng_orbitKernel_muBeta_le_and_tail_le
-- name    : ErschlerZheng.orbitKernel_muBeta_le_and_tail_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T06:39:48.169913+00:00
-- url     : https://prove2.me/theorems/105198cd-e74b-429d-91eb-e83c69dd304d
-- title:
--   Proposition 7.18 — for k_n = A⌊log₂ n⌋, P_{μ_β}(x, y) ⩽ C d^{−1−β}(log₂ d)^{2A(1−1/D+β)}(log₂log₂ d)^{1+1/D}, with the matching tail and truncated second-moment bounds
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $1 - \frac1D < \beta < 1$, and let $A$ be a positive integer divisible by $D$. Let $P$ be the transition kernel induced by $\mu_\beta$ (`muBeta`) with $k_n = A\lfloor\log_2 n\rfloor$ (`kLog A`) on the orbit $1^\infty \cdot G_\omega$ (`orbitKernel … oneRay`), and write $d(x, y)$ for the Schreier distance (`orbitDist`). Then there is a constant $C$ such that:
--
--   1. for all $x, y$ in the orbit with $d(x, y) \ge 4$,
--   $$P(x, y) \le C\, d(x,y)^{-1-\beta} (\log_2 d(x,y))^{2A(1-\frac1D+\beta)} (\log_2\log_2 d(x,y))^{1+\frac1D};$$
--   2. for every $x$ in the orbit and every real $r \ge 4$,
--   $$\sum_{y : d(x,y) \ge r} P(x, y) \le C r^{-\beta} (\log_2 r)^{2A(\beta-\frac1D)} (\log_2\log_2 r)^{1+\frac1D},$$
--   $$\sum_{y : d(x,y) \le r} d(x,y)^2 P(x, y) \le C r^{2-\beta} (\log_2 r)^{2A(\beta-\frac1D)} (\log_2\log_2 r)^{1+\frac1D}.$$
--
--   Erschler and Zheng, p. 46, Proposition 7.18: “Consider $\mu_\beta$ defined in (7.11) with $k_n = A\lfloor\log_2 n\rfloor$, where $1 - \frac1D < \beta < 1$ and $A$ is an integer divisible by $D$. There exists constant $C = C(D, \beta) < \infty$ such that: (i): For any $x, y \in 1^\infty \cdot G$, $P_{\mu_\beta}(x, y) \leqslant Cd_{\mathcal S}(x, y)^{-1-\beta}(\log_2 d_{\mathcal S}(x, y))^{2A(1-\frac1D+\beta)}(\log_2\log_2 d_{\mathcal S}(x, y))^{1+\frac1D}$. (ii): For any $x \in 1^\infty \cdot G$, $\sum_{y : d_{\mathcal S}(x,y) \geqslant r} P_{\mu_\beta}(x, y) \leqslant Cr^{-\beta}(\log_2 r)^{2A(\beta-\frac1D)}(\log_2\log_2 r)^{1+\frac1D}$. $\sum_{y : d_{\mathcal S}(x,y) \leqslant r} d_{\mathcal S}(x, y)^2P_{\mu_\beta}(x, y) \leqslant Cr^{2-\beta}(\log_2 r)^{2A(\beta-\frac1D)}(\log_2\log_2 r)^{1+\frac1D}$.”
--
--   The bounds are asserted for $d(x, y) \ge 4$ and $r \ge 4$: the printed right sides are undefined at distances $0$ and $1$ and radii below $2$, and for some $\omega$ and $A$ no constant gives the tail or the second-moment bound for every $r > 2$ ([`ErschlerZheng.not_forall_tsum_orbitKernel_muBeta_le_of_two_lt`](https://prove2.me/theorems/e4bd115c-b7cb-4948-9a28-9c0a7de3cbfc), [`ErschlerZheng.not_forall_tsum_orbitDist_sq_mul_orbitKernel_muBeta_le_of_two_lt`](https://prove2.me/theorems/367a5e77-0de2-490e-a713-d3d367dc2bad)). $A$ is taken positive, as $k_n > 0$ requires. The constant is chosen after $\omega$ and $A$, the standing parameters of §7 ($\omega$ from §7.2, p. 35; $A$ with $k_n = A\lfloor\log_2 n\rfloor$, p. 42). The paper's $C = C(D, \beta)$ lists the parameters the proposition introduces, not a uniformity in $\omega$ and $A$, and the constant of its proof grows with $A$: in (i) through the factor $k_n^{1+1/D}$ (p. 47: “$\leqslant AC_\beta 2^{-\frac1D\ell(x,y)+3} \ldots$”), and in (ii) through $k_{n_0}^{1+1/D}$, absorbed into $C'$ (p. 48). The sums over $y$ are over the orbit, and $\log_2$ is `Real.logb 2`.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 46, Proposition 7.18

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem orbitKernel_muBeta_le_and_tail_le (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    (β : ℝ) (hβ1 : 1 - 1 / (D : ℝ) < β) (hβ2 : β < 1) (A : ℕ) (hA : 0 < A) (hDA : D ∣ A) :
    ∃ C : ℝ,
      (∀ x y : orbitOne ω, 4 ≤ orbitDist ω x y →
        orbitKernel (grigorchuk ω) (muBeta D ω (kLog A) β) oneRay x y ≤
          C * orbitDist ω x y ^ (-1 - β) *
            Real.logb 2 (orbitDist ω x y) ^ (2 * (A : ℝ) * (1 - 1 / (D : ℝ) + β)) *
            Real.logb 2 (Real.logb 2 (orbitDist ω x y)) ^ (1 + 1 / (D : ℝ))) ∧
      (∀ x : orbitOne ω, ∀ r : ℝ, 4 ≤ r →
        ∑' y : orbitOne ω,
            (if r ≤ orbitDist ω x y then
              orbitKernel (grigorchuk ω) (muBeta D ω (kLog A) β) oneRay x y else 0) ≤
          C * r ^ (-β) * Real.logb 2 r ^ (2 * (A : ℝ) * (β - 1 / (D : ℝ))) *
            Real.logb 2 (Real.logb 2 r) ^ (1 + 1 / (D : ℝ))) ∧
      ∀ x : orbitOne ω, ∀ r : ℝ, 4 ≤ r →
        ∑' y : orbitOne ω,
            (if orbitDist ω x y ≤ r then
              orbitDist ω x y ^ 2 * orbitKernel (grigorchuk ω) (muBeta D ω (kLog A) β) oneRay x y
            else 0) ≤
          C * r ^ (2 - β) * Real.logb 2 r ^ (2 * (A : ℝ) * (β - 1 / (D : ℝ))) *
            Real.logb 2 (Real.logb 2 r) ^ (1 + 1 / (D : ℝ)) := by
  sorry

end ErschlerZheng
