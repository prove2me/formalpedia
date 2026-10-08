-- Prove2me | Theorems.Thm_CongestionPoA_SymSum_theorem3_sum_le
-- name    : CongestionPoA.SymSum.theorem3_sum_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:51:29.598002+00:00
-- url     : https://prove2.me/theorems/2b394b5c-aa2a-4cf5-b15d-6c8003f515f6
-- title:
--   Theorem 3 — symmetric linear games: pure price of anarchy of the average social cost $\le\frac{5N-2}{2N+1}$
-- statement:
--   Let $G$ be a symmetric congestion game with $N\ge1$ players and linear latencies $f_e(k)=a_ek+b_e$, $a_e,b_e\ge0$. For every pure Nash equilibrium $A$ and every pure strategy profile $P$,
--   $$\mathrm{SUM}(A)\le\frac{5N-2}{2N+1}\,\mathrm{SUM}(P).$$
--   Equivalently, the pure price of anarchy of the average social cost of symmetric linear congestion games with $N$ players is at most $(5N-2)/(2N+1)$.
--
--   The constant is $1$ for a single player, $8/5$ for two, $13/7$ for three, and increases to the asymmetric value $5/2$ as $N\to\infty$.
--
--   **Formalization Note** The bound for every profile $P$ is equivalent to the bound on the ratio to the optimum $\min_P\mathrm{SUM}(P)$, which is attained; no division by the optimum is needed. Players are $\{0,\dots,N-1\}$.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 3, Theorem 3 (proof on PDF pp. 3–4)

import Mathlib
import Definitions.Def_CongestionPoA_SymSum_Model

namespace CongestionPoA.SymSum

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 3, Theorem 3: for linear symmetric congestion games, the pure price of anarchy of the average
social cost is at most `(5N − 2)/(2N + 1)`, `N` the number of players. Stated as: for every pure
Nash equilibrium `A` and every pure strategy profile `P`, `SUM(A) ≤ ((5N − 2)/(2N + 1))·SUM(P)`.

**Formalization Note.** Since `opt = min_P SUM(P)` is attained (finitely many profiles), the bound for
every profile `P` is equivalent to `PA ≤ (5N − 2)/(2N + 1)`, without dividing by `opt`. Linear means
`f_e(k) = a_e k + b_e` with `a_e, b_e ≥ 0` (`IsLinear`); symmetric means all players share one
strategy set (`IsSymmetric`). Players are `Fin N` with `1 ≤ N`; the constant is computed in `ℝ`. -/
theorem theorem3_sum_le {N : ℕ} (hN : 1 ≤ N) {E : Type*} [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame (Fin N) E) (hlin : CongestionPoA.AsymSum.IsLinear G) (hsym : IsSymmetric G)
    (A P : Fin N → Finset E) (hA : CongestionPoA.AsymSum.IsPureNash G A) (hP : CongestionPoA.AsymSum.IsProfile G P) :
    CongestionPoA.AsymSum.sumCost G A ≤ (5 * (N : ℝ) - 2) / (2 * (N : ℝ) + 1) * CongestionPoA.AsymSum.sumCost G P := by sorry

end CongestionPoA.SymSum
