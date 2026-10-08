-- Prove2me | Theorems.Thm_DermanDenumerable_AvgCost_theorem4
-- name    : DermanDenumerable.AvgCost.theorem4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:20:59.916383+00:00
-- url     : https://prove2.me/theorems/ff4da6d9-cb1f-4e0a-9e03-93088f60f02b
-- title:
--   Theorem 4 — every limit point of policy improvement is a rule of C'' optimal over C
-- statement:
--   Assume conditions (A), (B), (C), (E) and (F) for a Markovian decision process on a denumerable state space $I$ with finitely many decisions per state and bounded costs. Let $\{g^R, v_j^R\}$ be the uniformly bounded solutions of (2) given by (E), and let $R_1, R_2, \dots$ be any sequence of policy improvement iterations starting from an arbitrary $R_1 \in C''$: the decisions of $R_{n+1}$ minimize
--   $$w_{ik} + \sum_{j\in I} q_{ij}(k) v_j^{R_n}$$
--   at every state $i$. Then:
--
--   1. the sequence has a limit point $R^* \in C''$, i.e. a subsequence $R_{n_\nu}$ whose decision at each state equals that of $R^*$ for all large $\nu$;
--   2. every limit point $R^*$ is optimal over $C$: $Q_{R^*}(i) \le Q_R(i)$ for every rule $R \in C$ and every $i \in I$;
--   3. for every limit point $R^*$ and every $i$, $g^{R_n} \to Q_{R^*}(i)$ as $n \to \infty$.
--
--   This is the paper's main theorem: on a denumerable state space, the policy improvement procedure "converges to a rule $R^* \in C$ which is optimal over $C$".
--
--   **Formalization Note.** The paper's "converges" is read as items 1–2: its proof chooses a subsequence converging to $R^*$ and never shows that the whole sequence converges, which can fail when the minimization has ties. Item 3 records the convergence of the values $g^{R_n}$ that the proof establishes ($g^{R_n} \downarrow g^* = Q_{R^*}$). Condition (D) is implied by (E) and is not a separate hypothesis. The sequence is indexed from $0$: `R 0` is the paper's $R_1$.
-- source:
--   Derman, Denumerable State Markovian Decision Processes—Average Cost Criterion, Ann. Math. Statist. 37(6) (1966), p. 1552, Theorem 4 (procedure and (F) on p. 1551)

import Mathlib
import Definitions.Def_DermanDenumerable_AvgCost_Model
open scoped Topology
open Filter SennottDP.AvgFinite

namespace DermanDenumerable.AvgCost

/-- Derman (1966), Theorem 4, p. 1552: under (A), (B), (C), (E) (hence (D)) and (F), let `R_1, R_2, ⋯`
be any sequence of policy improvement iterations (relative to the family `{g^R, v^R}` of (E)) from an
arbitrary initial rule of `C''`. Then (i) the sequence has a limit point `R*` in `C''`; (ii) every
limit point `R*` is optimal over the class `C` of all rules; and (iii) `g^{R_n}` converges to the
optimal average cost `Q_{R*}(i)`. -/
theorem theorem4 {S Act : Type} [Countable S] (M : MDC S Act)
    (w : S → Act → ℝ) (hB : CostBounded M w) (hC : CondC M) (gR : StationaryPolicy M → ℝ)
    (vR : StationaryPolicy M → S → ℝ) (hE : IsUniformEvaluation M w gR vR) (hF : CondF M)
    (R : ℕ → StationaryPolicy M) (hR : IsPISequence M w vR R) :
    (∃ e : StationaryPolicy M, IsLimitPoint R e) ∧
      ∀ e : StationaryPolicy M, IsLimitPoint R e →
        OptimalOverC w e.toPolicy ∧
          ∀ i : S, Tendsto (fun n : ℕ => gR (R n)) atTop (𝓝 (avgCostR e.toPolicy w i)) := by sorry

end DermanDenumerable.AvgCost
