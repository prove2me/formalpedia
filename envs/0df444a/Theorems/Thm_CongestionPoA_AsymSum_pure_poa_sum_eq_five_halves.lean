-- Prove2me | Theorems.Thm_CongestionPoA_AsymSum_pure_poa_sum_eq_five_halves
-- name    : CongestionPoA.AsymSum.pure_poa_sum_eq_five_halves
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:49:11.420272+00:00
-- url     : https://prove2.me/theorems/b5078e9f-784d-44f5-87a6-cf6255b38e5d
-- title:
--   Theorems 1–2 — the pure price of anarchy of the average social cost of linear congestion games is 5/2
-- statement:
--   For linear congestion games, the pure price of anarchy of the average social cost is exactly $5/2$. Precisely, with latencies $f_e(k)=a_ek+b_e$, $a_e,b_e\ge0$:
--
--   1. (Theorem 1) in every linear congestion game with finitely many players and facilities, every pure Nash equilibrium $A$ and every pure strategy profile $P$ satisfy
--   $$\mathrm{SUM}(A)\le\frac52\,\mathrm{SUM}(P);$$
--   2. (Theorem 2) for every $N\ge3$ there are a linear congestion game with $N$ players, a pure Nash equilibrium $A$ and an optimal pure strategy profile $P$ with $\mathrm{SUM}(P)>0$ and $\mathrm{SUM}(A)=\frac52\,\mathrm{SUM}(P)$.
--
--   The first part bounds the price of anarchy by $5/2$; the second shows that the bound is attained for every number of players $N\ge3$, so $5/2$ is the exact worst case. This is the "$5/2$" entry for asymmetric games and the average social cost in the paper's table of results.
--
--   **Formalization Note** The bound is stated multiplicatively, for every pure strategy profile $P$, which is equivalent to the ratio bound and avoids dividing by $\mathrm{opt}$. In the first part, players and facilities range over finite types in the lowest universe. In the second part, $\mathrm{SUM}(P)>0$ excludes the all-zero latency game, where the equality is trivial.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 3, Theorem 1 and Theorem 2

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model

namespace CongestionPoA.AsymSum

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 3, Theorem 1 and Theorem 2 together (the abstract's "the price of anarchy is 5/2" for pure
equilibria and the average social cost):

1. (Theorem 1) in every linear congestion game, every pure Nash equilibrium `A` and every pure
   strategy profile `P` satisfy `SUM(A) ≤ (5/2)·SUM(P)`;
2. (Theorem 2) for every `N ≥ 3` there is a linear congestion game with `N` players, a pure Nash
   equilibrium `A` and an optimal pure strategy profile `P` with `0 < SUM(P)` and
   `SUM(A) = (5/2)·SUM(P)`.

**Formalization Note.** Linear latencies are `f_e(k) = a_e k + b_e` with `a_e, b_e ≥ 0` (Sect. 2,
§1.1). The bound is stated multiplicatively, for every feasible `P`, which is equivalent to
`PA ≤ 5/2` and avoids dividing by `opt`. In the second part `0 < SUM(P)` excludes the all-zero
latency game, where `0 = (5/2)·0` holds trivially. Player and facility types in the first part range over
`Type` (universe 0), with finitely many players and facilities. -/
theorem pure_poa_sum_eq_five_halves :
    (∀ {ι E : Type} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
        (G : CongestionGame ι E) (A P : ι → Finset E),
        IsLinear G → IsPureNash G A → IsProfile G P → sumCost G A ≤ 5 / 2 * sumCost G P) ∧
    (∀ N : ℕ, 3 ≤ N →
      ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (G : CongestionGame (Fin N) E)
        (A P : Fin N → Finset E),
        IsLinear G ∧ IsPureNash G A ∧ IsProfile G P ∧
          (∀ Q : Fin N → Finset E, IsProfile G Q → sumCost G P ≤ sumCost G Q) ∧
          0 < sumCost G P ∧ sumCost G A = 5 / 2 * sumCost G P) := by sorry

end CongestionPoA.AsymSum
