-- Prove2me | Theorems.Thm_CongestionPoA_AsymSum_theorem1_sum_le_five_halves
-- name    : CongestionPoA.AsymSum.theorem1_sum_le_five_halves
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:48:48.010092+00:00
-- url     : https://prove2.me/theorems/5d822064-50b5-4859-bba9-c39e9e75e801
-- title:
--   Theorem 1 — pure price of anarchy of the average social cost is at most 5/2
-- statement:
--   For linear congestion games, the pure price of anarchy of the average social cost is at most $5/2$.
--
--   Precisely: let $G$ be a congestion game in which every facility $e$ has a latency $f_e(k)=a_ek+b_e$ with $a_e,b_e\ge0$. For every pure Nash equilibrium $A$ of $G$ and every pure strategy profile $P$ of $G$,
--   $$\mathrm{SUM}(A)\le\frac52\,\mathrm{SUM}(P).$$
--
--   Taking $P$ to be an optimal profile, this says that the pure price of anarchy $\sup_A \mathrm{SUM}(A)/\mathrm{opt}$, with $\mathrm{opt}=\min_P\mathrm{SUM}(P)$, is at most $5/2$, for any number of players and any (possibly asymmetric) strategy sets.
--
--   **Formalization Note** The bound is stated multiplicatively for every pure strategy profile $P$, which is equivalent to the ratio bound (the minimum is over finitely many profiles) and avoids dividing by $\mathrm{opt}$, which may be $0$. If some player has no strategy, no profile exists and the statement is vacuous, as in the paper. The paper's proof displays only the identity latency $f_e(k)=k$ and states that it extends to the affine case; the statement is the affine case.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 3, Theorem 1

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model

namespace CongestionPoA.AsymSum

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 3, Theorem 1: for linear congestion games, the pure price of anarchy of the average social
cost is at most `5/2`. Stated multiplicatively: for every pure Nash equilibrium `A` and every pure
strategy profile `P`, `SUM(A) ≤ (5/2)·SUM(P)`.

**Formalization Note.** Linear latencies are `f_e(k) = a_e k + b_e` with `a_e, b_e ≥ 0` (Sect. 2,
§1.1; the paper's proof displays only `f_e(k) = k`). The price of anarchy
`PA = sup_A SUM(A)/opt`, `opt = min_P SUM(P)`, is at most `5/2` exactly when the inequality holds for
every Nash `A` and every feasible `P` (the minimum is over finitely many profiles); the statement
avoids dividing by `opt`, which may be `0`. If some player has no strategy, no profile exists and the
statement is vacuous, as in the paper. -/
theorem theorem1_sum_le_five_halves {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (A P : ι → Finset E)
    (hlin : IsLinear G) (hA : IsPureNash G A) (hP : IsProfile G P) :
    sumCost G A ≤ 5 / 2 * sumCost G P := by sorry

end CongestionPoA.AsymSum
