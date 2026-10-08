-- Prove2me | Theorems.Thm_CongestionPoA_SymMax_theorem1_sum_le_five_halves
-- name    : CongestionPoA.SymMax.theorem1_sum_le_five_halves
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:11:54.993207+00:00
-- url     : https://prove2.me/theorems/74f3a792-cda7-4521-93e4-80a75fa21c20
-- title:
--   Theorem 1 — linear congestion games: $\mathrm{SUM}(A)\le\frac52\mathrm{SUM}(P)$ at pure Nash equilibria
-- statement:
--   For linear congestion games, the pure price of anarchy of the average social cost is at most $5/2$: if the latencies are $f_e(k)=a_ek+b_e$ with $a_e,b_e\ge0$, then for every pure Nash equilibrium $A$ and every pure strategy profile $P$,
--   $$\mathrm{SUM}(A)\;\le\;\tfrac52\,\mathrm{SUM}(P).$$
--
--   The proof of Theorem 7 invokes this bound ("We can now use Theorem 1") to replace $\mathrm{SUM}(A)$ by $\frac52\mathrm{SUM}(P)$.
--
--   **Formalization Note** The ratio form $\sup_A \mathrm{SUM}(A)/\mathrm{opt}\le 5/2$ is equivalent to the inequality for every feasible $P$, because the optimum is a minimum over finitely many profiles; the statement avoids dividing by the optimum. Symmetry is not assumed. The paper's proof displays only $f_e(k)=k$. The same theorem is drafted in mission I of this series.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 3, Theorem 1

import Mathlib
import Definitions.Def_CongestionPoA_SymMax_Model

namespace CongestionPoA.SymMax

/-- Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*, STOC 2005,
PDF p. 3, Theorem 1: for linear congestion games, the pure price of anarchy of the average social
cost is at most `5/2`. Stated multiplicatively: for every pure Nash equilibrium `A` and every pure
strategy profile `P`, `SUM(A) ≤ (5/2)·SUM(P)`. Invoked in the proof of Theorem 7 (PDF p. 5, "We can
now use Theorem 1").

**Formalization Note.** Linear latencies are `f_e(k) = a_e k + b_e` with `a_e, b_e ≥ 0` (Sect. 2,
§1.1; the paper's proof displays only `f_e(k) = k`). The price of anarchy
`PA = sup_A SUM(A)/opt`, `opt = min_P SUM(P)`, is at most `5/2` exactly when the inequality holds for
every Nash `A` and every feasible `P` (the minimum is over finitely many profiles); the statement
avoids dividing by `opt`, which may be `0`. Symmetry is not assumed: Theorem 1 is about all
(asymmetric) linear congestion games. -/
theorem theorem1_sum_le_five_halves {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (A P : ι → Finset E)
    (hlin : IsLinear G) (hA : IsPureNash G A) (hP : IsProfile G P) :
    sumCost G A ≤ 5 / 2 * sumCost G P := by sorry

end CongestionPoA.SymMax
