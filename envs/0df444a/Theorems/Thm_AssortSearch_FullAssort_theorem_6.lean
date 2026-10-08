-- Prove2me | Theorems.Thm_AssortSearch_FullAssort_theorem_6
-- name    : AssortSearch.FullAssort.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:11.03573+00:00
-- url     : https://prove2.me/theorems/a182b907-a047-4a68-b6fa-d2833094b3fd
-- title:
--   Theorem 6 — under overlapping-assortment search, the full assortment is optimal for every search cost $b \le \bar b$
-- statement:
--   Consider the overlapping assortment model with preferences $v_1, \dots, v_n > 0$ and no-purchase preference $v_0 > 0$, Gumbel scale $\mu > 0$, margins $m_1, \dots, m_n \in \mathbb R$ that are monotone in net utility ($m_j \ge m_k$ whenever $v_j \ge v_k$, the standing assumption of §3, p. 6), and an operational cost function $c$ that is concave and increasing on $[0,1]$ with $c(0) \ge 0$. For a search cost $b$ and an assortment $S \subseteq N$, let $\pi_b(S) = \sum_{i \in S}[m_i q_i^{so}(S) - c(q_i^{so}(S))]$ be the retailer's profit (13). Suppose the full assortment yields a positive profit,
--
--   $$\pi(N) = \sum_{i=1}^n \big[m_i q_i^m(N) - c(q_i^m(N))\big] > 0 .$$
--
--   Then there is a threshold search cost $\bar b > 0$ such that for every search cost $0 < b \le \bar b$ the full assortment is optimal:
--
--   $$\pi_b(S) \le \pi_b(N) \qquad \text{for every } S \subseteq N .$$
--
--   With the full assortment no consumer searches, so its profit does not depend on $b$. The theorem says that when search is cheap enough, preventing search by carrying every variant beats any narrower assortment, however profitable its individual variants are.
--
--   **Formalization Note** The hypothesis $c(0) \ge 0$ is added; the paper does not state the value of $c(0)$, and without it the theorem is false (with $n = 2$, $v_1 = v_2 = 1$, $v_0 = 0.1$, $m_1 = m_2 = 2$ and the concave increasing $c(q) = -1 + 2q^{0.1}$, one has $\pi(N) \approx 0.19 > 0$ while $\pi_b(\{1\}) \to -c(0) = 1$ as $b \to 0$). The threshold $\bar b$ is one number that works for all $S$ at once, and $b$ ranges over positive search costs. The paper's $S = N$ case has no search, so $q_i^{so}(N) = q_i^m(N)$.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 18 (PDF 20), Theorem 6

import Mathlib
import Definitions.Def_AssortSearch_FullAssort_Model

namespace AssortSearch.FullAssort

/-- Theorem 6 (p. 18): if the full assortment yields a positive profit, there is a threshold
search cost `b̄ > 0` such that the full assortment is optimal for every search cost
`0 < b ≤ b̄`: no assortment `S ⊆ N` earns more than `N`. Margins are monotone in the variants'
net utility, `m_j ≥ m_k` if `v_j ≥ v_k` (§3, p. 6). The hypothesis `0 ≤ c 0` is added. -/
theorem theorem_6 {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (v : Fin n → ℝ) (hv : ∀ i, 0 < v i)
    (v0 : ℝ) (hv0 : 0 < v0) (m : Fin n → ℝ) (hm : ∀ j k, v k ≤ v j → m k ≤ m j) (c : ℝ → ℝ)
    (hc_conc : ConcaveOn ℝ (Set.Icc 0 1) c) (hc_mono : MonotoneOn c (Set.Icc 0 1))
    (hc0 : 0 ≤ c 0) (hpos : 0 < fullProfit v v0 m c) :
    ∃ bbar : ℝ, 0 < bbar ∧ ∀ b : ℝ, 0 < b → b ≤ bbar →
      ∀ S : Finset (Fin n), profitSO μ v v0 m c b S ≤ profitSO μ v v0 m c b Finset.univ := by sorry

end AssortSearch.FullAssort
