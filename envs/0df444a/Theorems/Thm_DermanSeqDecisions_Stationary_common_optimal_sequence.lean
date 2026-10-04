-- Prove2me | Theorems.Thm_DermanSeqDecisions_Stationary_common_optimal_sequence
-- name    : DermanSeqDecisions.Stationary.common_optimal_sequence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:45:38.921502+00:00
-- url     : https://prove2.me/theorems/0e7b7e6c-de9b-4539-9a19-27dd9e937fef
-- title:
--   One procedure $R^* \in C''$ is $\alpha_v$-discount optimal along a sequence $\alpha_v \to 1$
-- statement:
--   Let the states and the decisions be finite sets, every decision being available in every state, with transition probabilities $q_{ij}(k)$ and costs $w_{ik} \ge 0$, and let $V_R(i, \alpha) = \sum_{t \ge 0} \alpha^t W_t$.
--
--   There are a deterministic stationary procedure $R^* \in C''$ and a sequence $(\alpha_v)_{v \ge 1}$ in $(0, 1)$ with $\lim_{v \to \infty} \alpha_v = 1$ such that, for every $v$,
--   $$V_{R^*}(i, \alpha_v) \le V_R(i, \alpha_v) \qquad \text{for every procedure } R \in C \text{ and every state } i.$$
--
--   In Derman's proof this is where the finiteness of $C''$ enters: the discount-optimal procedures $R_\alpha$ range over finitely many maps, so one of them recurs along a sequence of discount factors tending to $1$.
--
--   **Formalization Note** $V_R(i, \alpha)$ is `discCost θ α i` in $[0, \infty]$; $C$ is the type of all policies of the published model. The sequence is indexed by $\mathbb N$ and need not be monotone.
-- source:
--   Derman, On Sequential Decisions and Markov Chains, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, p. 19, §2, proof of Theorem 1

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_SennottDP_AvgFinite_Criteria

open scoped ENNReal NNReal Topology
open SennottDP.AvgFinite Filter

namespace DermanSeqDecisions.Stationary

/-- One procedure `R* ∈ C″` is discount-optimal along a sequence `α_v → 1` (Derman, *On
Sequential Decisions and Markov Chains*, Management Science 9(1):16–24 (1962),
DOI 10.1287/mnsc.9.1.16, §2, proof of Theorem 1, p. 19, unnumbered). States `S` and decisions
`Act` are finite, every decision is available in every state, and the costs are nonnegative.
There are a deterministic stationary procedure `R*` (a map `f` from states to decisions) and a
sequence `α_v ∈ (0, 1)` with `α_v → 1` such that, for every `v`, `R*` is `α_v`-discount optimal:
`V_{R*}(i, α_v) ≤ V_R(i, α_v)` for every procedure `R ∈ C` and every initial state `i`.

**Formalization Note.** `V_R(i, α)` is `discCost θ α i ∈ [0, ∞]`, `C` is `Policy M` (all
history-dependent randomized procedures) and `C″` is `StationaryPolicy M`. The sequence is not
required to be monotone, as on the page. -/
theorem common_optimal_sequence {S : Type*} {Act : Type*} [Fintype S] [Nonempty S]
    [Fintype Act] [Nonempty Act]
    (M : MDC S Act) (hA : ∀ i, M.A i = Finset.univ) :
    ∃ f : StationaryPolicy M, ∃ αs : ℕ → ℝ,
      (∀ v, αs v ∈ Set.Ioo (0 : ℝ) 1) ∧ Tendsto αs atTop (𝓝 1) ∧
      ∀ v, ∀ θ : Policy M, ∀ i : S,
        discCost f.toPolicy (αs v) i ≤ discCost θ (αs v) i := by sorry

end DermanSeqDecisions.Stationary
