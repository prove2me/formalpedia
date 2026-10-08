-- Prove2me | Theorems.Thm_CongestionPoA_Mixed_mixed_poa_sum_le
-- name    : CongestionPoA.Mixed.mixed_poa_sum_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:07:42.580184+00:00
-- url     : https://prove2.me/theorems/c7938410-151c-4b09-83c4-8a180b4e6476
-- title:
--   Theorem 14 — the mixed price of anarchy of linear congestion games for the average social cost is at most (3+√5)/2
-- statement:
--   Consider a congestion game with players $N$, facilities $E$ and linear latencies $f_e(k) = a_e k + b_e$ with $a_e, b_e \ge 0$. Let $p$ be a mixed Nash equilibrium, in which the players randomize independently over their strategy sets $\Sigma_i$, and let $P$ be any pure strategy profile, $P_i \in \Sigma_i$. Then the sum of the players' expected costs at $p$ is at most $(3+\sqrt5)/2 \approx 2.618$ times the social cost of $P$:
--   $$\sum_{i \in N} \mathbb E[c_i] \le \frac{3 + \sqrt5}{2}\, \mathrm{SUM}(P), \qquad \mathrm{SUM}(P) = \sum_{i\in N} c_i(P).$$
--   Since $P$ is arbitrary, it may be an optimal profile, so the mixed price of anarchy of the average social cost is at most $(3+\sqrt5)/2$.
--
--   The pure price of anarchy of the same class is $5/2$ (Theorems 1 and 2); the mixed bound is the golden-ratio constant $\varphi^2 = (3+\sqrt5)/2$, the same value Awerbuch, Azar and Epstein obtained for weighted games.
--
--   **Formalization Note** The social cost of the mixed equilibrium is the first of the two options of Sect. 5, the sum of the expected costs of the players. The bound is stated against every feasible pure profile instead of as a ratio to the optimum, which is equivalent because there are finitely many pure profiles and avoids dividing by an optimum that may be $0$. Mixed equilibria are independent randomizations (`AGT.IsMixedNash` with payoffs $-c_i$); a correlated distribution on profiles is a different theorem.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 6, Theorem 14

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_CongestionPoA_Mixed_Model

namespace CongestionPoA.Mixed

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 6, Theorem 14: the mixed price of anarchy of linear congestion games for the average social
cost is at most `(3 + √5)/2 ≈ 2.618`. For every congestion game with linear latencies, every mixed
Nash equilibrium `σ` and every pure strategy profile `P`,
`Σᵢ E[cᵢ] ≤ ((3 + √5)/2)·SUM(P)`.

**Formalization Note.** "Linear" is the paper's `f_e(k) = a_e·k + b_e` with `a_e, b_e ≥ 0` (Sect. 2).
The social cost of the mixed equilibrium is the first option of Sect. 5, the sum of the players'
expected costs (`mixedSumCost`); the optimum is `opt = min_{P∈Σ} SUM(P)` over pure profiles (Sect. 2).
Bounding by `SUM(P)` for every feasible pure `P` is equivalent to `PA ≤ (3+√5)/2`, since there are
finitely many pure profiles; no ratio is formed, so `opt = 0` needs no special case. Mixed equilibria
are independent randomizations (`AGT.IsMixedNash` with payoff `−cost`); a correlated distribution on
profiles is not covered. -/
theorem mixed_poa_sum_le {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E) (hlin : CongestionPoA.AsymSum.IsLinear G)
    (σ : ∀ i, ↥(G.strategies i) → ℝ) (hσ : IsMixedNash G σ)
    (P : ι → Finset E) (hP : CongestionPoA.AsymSum.IsProfile G P) :
    mixedSumCost G σ ≤ (3 + Real.sqrt 5) / 2 * CongestionPoA.AsymSum.sumCost G P := by sorry

end CongestionPoA.Mixed
