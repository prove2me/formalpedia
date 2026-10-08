-- Prove2me | Theorems.Thm_DermanDenumerable_AvgCost_lemma2
-- name    : DermanDenumerable.AvgCost.lemma2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:21:12.037065+00:00
-- url     : https://prove2.me/theorems/f04ec11a-18b9-4f8c-84e4-1d412fe62125
-- title:
--   Lemma 2 — along policy improvement the gaps ε_i^{R_n} tend to 0 at every state
-- statement:
--   Assume (A), (B), (C), (E) and (F). Let $\{g^R, v^R_j\}$ be the uniformly bounded family of (E), and let $R_1, R_2, \dots$ be a sequence of policy improvement iterations starting from an arbitrary $R_1 \in C''$: for every $n$, the decisions $k_i'$ of $R_{n+1}$ minimize $w_{ik} + \sum_j q_{ij}(k) v_j^{R_n}$ at every state. With
--   $$\varepsilon_i^{R_n} = g^{R_n} + v_i^{R_n} - \Big(w_{ik_i'} + \sum_j q_{ij}(k_i') v_j^{R_n}\Big),$$
--   we have, for each $i \in I$,
--   $$\lim_{n\to\infty} \varepsilon_i^{R_n} = 0 .$$
--
--   The lemma says that the improvement step eventually stops finding improvements at each fixed state; it is the key step of Theorem 4.
--
--   **Formalization Note.** The improvement step is taken against the family $v^R$ of (E), as in the paper's definition of $\varepsilon_i^R$; ties among minimizing decisions are broken arbitrarily. Condition (D) is implied by (E) and is not a separate hypothesis. The sequence is indexed from $0$ in Lean.
-- source:
--   Derman, Denumerable State Markovian Decision Processes—Average Cost Criterion, Ann. Math. Statist. 37(6) (1966), pp. 1551–1552, Lemma 2 (ε_i^R and the procedure on p. 1551)

import Mathlib
import Definitions.Def_DermanDenumerable_AvgCost_Model
open scoped Topology
open Filter SennottDP.AvgFinite

namespace DermanDenumerable.AvgCost

/-- Derman (1966), Lemma 2, pp. 1551–1552: under (A), (B), (C), (E) (hence (D)) and (F), for any
sequence `R_1, R_2, ⋯` of policy improvement iterations (relative to the family `{g^R, v^R}` of (E))
starting from an arbitrary rule of `C''`, `lim_{n→∞} ε_i^{R_n} = 0` for every state `i`. -/
theorem lemma2 {S Act : Type} [Countable S] (M : MDC S Act)
    (w : S → Act → ℝ) (hB : CostBounded M w) (hC : CondC M) (gR : StationaryPolicy M → ℝ)
    (vR : StationaryPolicy M → S → ℝ) (hE : IsUniformEvaluation M w gR vR) (hF : CondF M)
    (R : ℕ → StationaryPolicy M) (hR : IsPISequence M w vR R) :
    ∀ i : S, Tendsto (fun n : ℕ => gap M w gR vR (R n) (R (n + 1)) i) atTop (𝓝 0) := by sorry

end DermanDenumerable.AvgCost
