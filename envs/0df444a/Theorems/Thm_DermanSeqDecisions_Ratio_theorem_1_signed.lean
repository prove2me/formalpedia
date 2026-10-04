-- Prove2me | Theorems.Thm_DermanSeqDecisions_Ratio_theorem_1_signed
-- name    : DermanSeqDecisions.Ratio.theorem_1_signed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:45:57.338168+00:00
-- url     : https://prove2.me/theorems/a990ba94-75ab-414e-ac0f-efbb90ef4e4d
-- title:
--   Theorem 1 (1) without the sign condition: a deterministic stationary procedure minimizes the average cost for any real costs
-- statement:
--   Consider a controlled Markov chain with finitely many states $0, \dots, L$ and decisions $d_1, \dots, d_K$, all available in every state, with transition probabilities $q_{ij}(k)$. Let $c = (c_{ik})$ be any real cost function, of either sign. For a procedure $R$ (history-dependent and randomized) and an initial state $i$, let $W_t$ be the expected cost at time $t$ and
--   $$Q_R(i) = \limsup_{T\to\infty} \frac1T \sum_{t=0}^T W_t .$$
--   Then there is a deterministic stationary procedure $R_1 \in C''$ (a fixed decision in each state) such that
--   $$Q_{R_1}(i) \le Q_R(i) \qquad \text{for every procedure } R \in C \text{ and every } i = 0, \dots, L .$$
--
--   This is Theorem 1 (1) of Derman (p. 18) with the positivity of the costs dropped, which the proof of Theorem 3 (p. 23) asserts to be unnecessary for Problem 1. It is applied there to the signed costs $w_{ik} = w'_{ik} - m\, w''_{ik}$.
--
--   **Formalization Note** The competitors range over all history-dependent randomized procedures. A single $R_1$ serves every initial state. The cost is an explicit real argument; the nonnegative cost field of Sennott's model plays no role.
-- source:
--   Derman, On Sequential Decisions and Markov Chains, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, p. 23, §4, proof of Theorem 3 (parenthetical remark), applied to Theorem 1 (1), p. 18

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_DermanSeqDecisions_Ratio_Criteria

open SennottDP.AvgFinite

namespace DermanSeqDecisions.Ratio

/-- **Theorem 1 (1) for costs of either sign** (Derman, *On Sequential Decisions and Markov
Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §4, proof of Theorem 3,
p. 23, using Theorem 1 (1), p. 18): "the hypothesis that `w_ik > 0` is unnecessary for Problem 1".

For every real cost function `c` there is a deterministic stationary procedure `f ∈ C″` whose
long-run average expected cost `Q_f(i)` is at most `Q_θ(i)` for every procedure `θ ∈ C` and
every initial state `i`; one `f` serves every initial state.

**Formalization Note.** `M.P` is Derman's `q_ij(k)`; `hA` says all decisions are available in
every state. The competitors `θ` range over all history-dependent randomized procedures
(`Policy M`). The cost `c` is an explicit argument with no sign condition; `M.C` plays no role. -/
theorem theorem_1_signed {S Act : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Act] [DecidableEq Act] (M : MDC S Act) (hA : ∀ s, M.A s = Finset.univ)
    (c : S → Act → ℝ) :
    ∃ f : StationaryPolicy M, ∀ θ : Policy M, ∀ i : S,
      avgCostR f.toPolicy i c ≤ avgCostR θ i c := by sorry

end DermanSeqDecisions.Ratio
