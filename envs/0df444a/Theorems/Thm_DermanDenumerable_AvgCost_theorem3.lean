-- Prove2me | Theorems.Thm_DermanDenumerable_AvgCost_theorem3
-- name    : DermanDenumerable.AvgCost.theorem3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:20:56.716112+00:00
-- url     : https://prove2.me/theorems/074672c1-c86a-4020-9058-594467ac262f
-- title:
--   Theorem 3 — under (A), (B), (C), (D), (E) some rule of C'' is optimal over C
-- statement:
--   Assume (A), (B), (C) and (E): for every $R \in C''$ there are real numbers $\{g^R, v_j^R\}$ solving (2) for $R$, bounded uniformly over $j \in I$ and $R \in C''$ (so (D) holds for every rule of $C''$). Then there exists a rule $R^* \in C''$ which is optimal over $C$:
--   $$Q_{R^*}(i) \le Q_R(i) \qquad \text{for every rule } R \in C \text{ and every } i \in I.$$
--
--   This is the existence result of the paper; Theorem 4 makes it constructive through policy improvement.
--
--   **Formalization Note.** (E) is stated with an explicit family $g^R$, $v^R$; (D) for each rule follows from it and is not a separate hypothesis.
-- source:
--   Derman, Denumerable State Markovian Decision Processes—Average Cost Criterion, Ann. Math. Statist. 37(6) (1966), p. 1550, Theorem 3

import Mathlib
import Definitions.Def_DermanDenumerable_AvgCost_Model
open scoped Topology
open Filter SennottDP.AvgFinite

namespace DermanDenumerable.AvgCost

/-- Derman (1966), Theorem 3, p. 1550: under (A), (B), (C) and (E) (which gives (D) for every rule of
`C''`), some rule `R* ∈ C''` is optimal over `C`. -/
theorem theorem3 {S Act : Type} [Countable S] (M : MDC S Act)
    (w : S → Act → ℝ) (hB : CostBounded M w) (hC : CondC M) (gR : StationaryPolicy M → ℝ)
    (vR : StationaryPolicy M → S → ℝ) (hE : IsUniformEvaluation M w gR vR) :
    ∃ e : StationaryPolicy M, OptimalOverC w e.toPolicy := by sorry

end DermanDenumerable.AvgCost
