-- Prove2me | Theorems.Thm_DermanDenumerable_AvgCost_remark_improvement
-- name    : DermanDenumerable.AvgCost.remark_improvement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:20:25.145128+00:00
-- url     : https://prove2.me/theorems/e9357425-cf7c-44d6-9673-3f1b76f6f765
-- title:
--   §4, remark after Lemma 1 — the improvement from R to R' is Σ_i π_i ε_i
-- statement:
--   In the setting of Lemma 1 (conditions (A), (B), (C); $R \in C''$ with a bounded solution $\{g, v_j\}$ of (2); $R'$ keeping $k_i$ or making the strict improvement (8) at each state), let
--   $$\varepsilon_i = \Big(w_{ik_i} + \sum_{j} q_{ij}(k_i) v_j\Big) - \Big(w_{ik_i'} + \sum_j q_{ij}(k_i') v_j\Big), \qquad i \in I,$$
--   so that $\varepsilon_i > 0$ on $I'$ and $\varepsilon_i = 0$ elsewhere, and let $\{\pi_i\}$ be the steady state probabilities of the Markov chain of $R'$, with transition probabilities $p_{ij} = q_{ij}(k_i')$. Then the series $\sum_i \pi_i \varepsilon_i$ converges absolutely and, for every initial state $l$,
--   $$Q_R(l) - Q_{R'}(l) = \sum_{i\in I} \pi_i \varepsilon_i .$$
--
--   The amount of improvement is thus a $\pi$-weighted sum of the local gaps. Lemma 2 applies this identity to consecutive iterates of the policy improvement procedure.
--
--   **Formalization Note.** $\pi_i$ is the published `steadyState`, the reciprocal $1/m_{ii}$ of the mean return time, as the paper's "steady state probabilities" of a positive recurrent chain. $I' = \emptyset$ is allowed here (both sides are then $0$).
-- source:
--   Derman, Denumerable State Markovian Decision Processes—Average Cost Criterion, Ann. Math. Statist. 37(6) (1966), p. 1550, §4, remark after Lemma 1

import Mathlib
import Definitions.Def_DermanDenumerable_AvgCost_Model
open scoped Topology
open Filter SennottDP.AvgFinite

namespace DermanDenumerable.AvgCost

/-- Derman (1966), §4, remark after Lemma 1, p. 1550: in the setting of Lemma 1, the improvement
`Q_R(l) − Q_{R'}(l)` equals `Σ_i π_i ε_i`, where `π_i` are the steady state probabilities of the chain
of `R'` and `ε_i = (w_{ik_i} + Σ_j q_ij(k_i) v_j) − (w_{ik_i'} + Σ_j q_ij(k_i') v_j)`; the series
converges absolutely. -/
theorem remark_improvement {S Act : Type} [Countable S] (M : MDC S Act)
    (w : S → Act → ℝ) (hB : CostBounded M w) (hC : CondC M) (e e' : StationaryPolicy M) (g : ℝ)
    (v : S → ℝ) (hv : BddFun v) (hD : IsEvaluation M w e g v)
    (h8 : ∀ i : S, e'.f i = e.f i ∨
      w i (e'.f i) + expNext M i (e'.f i) v < w i (e.f i) + expNext M i (e.f i) v) :
    Summable (fun i : S => (SennottDP.MarkovCost.steadyState (chainOf M e') i).toReal *
        (w i (e.f i) + expNext M i (e.f i) v - (w i (e'.f i) + expNext M i (e'.f i) v))) ∧
      ∀ l : S, avgCostR e.toPolicy w l - avgCostR e'.toPolicy w l =
        ∑' i : S, (SennottDP.MarkovCost.steadyState (chainOf M e') i).toReal *
          (w i (e.f i) + expNext M i (e.f i) v - (w i (e'.f i) + expNext M i (e'.f i) v)) := by sorry

end DermanDenumerable.AvgCost
