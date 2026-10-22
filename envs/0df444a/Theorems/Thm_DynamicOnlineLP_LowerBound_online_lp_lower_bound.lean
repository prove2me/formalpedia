-- Prove2me | Theorems.Thm_DynamicOnlineLP_LowerBound_online_lp_lower_bound
-- name    : DynamicOnlineLP.LowerBound.online_lp_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T20:29:27.348562+00:00
-- url     : https://prove2.me/theorems/4b783f9a-3a2e-4482-bcbc-7ef5e020b962
-- title:
--   Theorem 2 — no online algorithm for online LP in the random permutation model beats competitive ratio 1 − Ω(√(log m / B))
-- statement:
--   Consider online linear programming in the random permutation model: an instance has $n$ columns $(\pi_t,a_t)$ with $\pi_t\ge 0$ and $a_t\in[0,1]^m$ and a right-hand side $b\in\mathbb R^m$; the columns arrive in a uniformly random order $\sigma$; an online algorithm knows $n$ and $b$, sees each column when it arrives, and must choose $x_t\in[0,1]$ irrevocably so that $\sum_{s\le t}a_{i\sigma(s)}x_s\le b_i$ for all $i$; and $\mathrm{OPT}$ is the optimal value of the offline linear program $\max\{\sum_t\pi_tx_t:\sum_t a_{it}x_t\le b_i\ \forall i,\ 0\le x_t\le 1\}$.
--
--   **Theorem.** There are absolute constants $c>0$ and $K>0$ such that for every $m\ge 2$, every $B\ge K\log m$ and every online algorithm $A$ with $m$ constraints, there is an instance with $n$ columns, $\pi_t\ge 0$, $a_t\in[0,1]^m$ and $b_i=B$ for all $i$, on which
--
--   $$\mathbb E_\sigma\Bigl[\sum_{t=1}^n\pi_{\sigma(t)}x_t^A\Bigr]<\Bigl(1-c\sqrt{\frac{\log m}{B}}\Bigr)\,\mathrm{OPT}.$$
--
--   That is, no online algorithm achieves a competitive ratio better than $1-\Omega(\sqrt{\log m/B})$; equivalently, a competitive ratio $1-O(\varepsilon)$ requires $B=\min_i b_i\ge\Omega(\log m/\varepsilon^2)$. Together with the paper's Theorem 1 (the dynamic learning algorithm is $1-O(\varepsilon)$ competitive when $B\ge\Omega(m\log(n/\varepsilon)/\varepsilon^2)$), it shows that a dependence of the right-hand-side size on the number of constraints $m$ is unavoidable, complementing Kleinberg's single-constraint bound $B\ge\Omega(1/\varepsilon^2)$.
--
--   **Formalization Note** The paper writes $\Omega(\cdot)$; it is formalized with absolute constants $c, K$ chosen before $m$, $B$, the algorithm and the instance. $\log$ is the natural logarithm (a change of base only rescales $c$ and $K$). The threshold $B\ge K\log m$ is the formal content of "when $B\le\log(m)/\varepsilon^2$" for $\varepsilon\le 1/\sqrt K$; without it the right-hand side can be negative. The quantifiers are those of the page: the algorithm is fixed first, then the instance is chosen, and the instance must use the given capacity level $B$ on every row ($\min_i b_i=B$). $B$ is any real number, not necessarily an integer. Algorithms are deterministic and fractional (see the definition file); randomized algorithms reduce to them by averaging their decisions. The expectation over $\sigma$ is the average over all $n!$ permutations. The inequality is strict, as in "less than" on the page.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 878, Theorem 2 (second, "equivalently" form); proof §4, pp. 885–886, and Appendix C, pp. 888–889

import Mathlib
import Definitions.Def_DynamicOnlineLP_LowerBound_OnlineLP

namespace DynamicOnlineLP.LowerBound

/-- Agrawal–Wang–Ye 2014, Theorem 2 (p. 878), second form: no online algorithm for the online LP
(2) in the random permutation model achieves a competitive ratio better than
`1 - Ω(√(log m / B))`. There are absolute constants `c, K > 0` such that for every number of
constraints `m ≥ 2` and every capacity level `B ≥ K log m`, and every online algorithm `A`, some
instance with `π_t ≥ 0`, `a_t ∈ [0,1]^m` and `b_i = B` for all `i` satisfies
`E_σ[∑_t π_{σ(t)} x_t] < (1 - c √(log m / B)) · OPT`. -/
theorem online_lp_lower_bound :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
      ∀ (m : ℕ) (B : ℝ), 2 ≤ m → K * Real.log (m : ℝ) ≤ B →
        ∀ A : OnlineAlgorithm m,
          ∃ (n : ℕ) (π : Fin n → ℝ) (a : Fin n → Fin m → ℝ),
            (∀ t, 0 ≤ π t) ∧ (∀ t i, 0 ≤ a t i ∧ a t i ≤ 1) ∧
              expectedOnlineValue A π a (fun _ => B) <
                (1 - c * Real.sqrt (Real.log (m : ℝ) / B)) * OPT π a (fun _ => B) := by sorry

end DynamicOnlineLP.LowerBound
