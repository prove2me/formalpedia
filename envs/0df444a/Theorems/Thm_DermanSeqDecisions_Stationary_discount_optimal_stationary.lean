-- Prove2me | Theorems.Thm_DermanSeqDecisions_Stationary_discount_optimal_stationary
-- name    : DermanSeqDecisions.Stationary.discount_optimal_stationary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:44:38.289227+00:00
-- url     : https://prove2.me/theorems/568cb85d-b825-461a-acdf-3267eb47f754
-- title:
--   For each discount factor, some procedure in $C''$ is discount optimal over all of $C$
-- statement:
--   Let the states and the decisions be finite sets, every decision being available in every state, with transition probabilities $q_{ij}(k)$ and costs $w_{ik} \ge 0$. For a procedure $R$ and $0 < \alpha < 1$ let $V_R(i, \alpha) = \sum_{t \ge 0} \alpha^t W_t$ be its expected discounted cost from $X_0 = i$.
--
--   Then for every $\alpha \in (0, 1)$ there is a deterministic stationary procedure $R_\alpha \in C''$, that is, a map $f$ assigning a decision $f(i)$ to each state $i$ and used at every time regardless of the past, such that
--   $$V_{R_\alpha}(i, \alpha) \le V_R(i, \alpha) \qquad \text{for every procedure } R \in C \text{ and every state } i.$$
--   Here $C$ is the class of all history-dependent randomized procedures, so $V_{R_\alpha}(i, \alpha) = \min_{R \in C} V_R(i, \alpha)$, with one $R_\alpha$ for all initial states.
--
--   This is the discounted version of Theorem 1 and the first step of its proof.
--
--   **Formalization Note** $V_R(i, \alpha)$ is `discCost θ α i` in $[0, \infty]$. Since `discCost` is defined for every real $\alpha$, the hypothesis $0 < \alpha < 1$ is explicit.
-- source:
--   Derman, On Sequential Decisions and Markov Chains, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, pp. 18–19, §2, proof of Theorem 1 (R_α ∈ C″)

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_SennottDP_AvgFinite_Criteria

open scoped ENNReal NNReal
open SennottDP.AvgFinite

namespace DermanSeqDecisions.Stationary

/-- A discount-optimal procedure in `C″` (Derman, *On Sequential Decisions and Markov Chains*,
Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §2, proof of Theorem 1,
pp. 18–19, unnumbered). States `S` and decisions `Act` are finite, every decision is available
in every state, and the costs `w_ik = M.C i k` are nonnegative. For every discount factor
`0 < α < 1` there is a deterministic stationary procedure `R_α ∈ C″` (a map `f` from states to
decisions) such that `V_{R_α}(i, α) ≤ V_R(i, α)` for every procedure `R ∈ C` (history-dependent
and randomized) and every initial state `i`, where `V_R(i, α) = ∑_t α^t W_t`.

**Formalization Note.** `V_R(i, α)` is `discCost θ α i ∈ [0, ∞]`; `C` is `Policy M` and `C″` is
`StationaryPolicy M` via `.toPolicy`. One `f` serves every initial state. `discCost` is defined
for every real `α`, so the range `0 < α < 1` is an explicit hypothesis. -/
theorem discount_optimal_stationary {S : Type*} {Act : Type*} [Fintype S] [Nonempty S]
    [Fintype Act] [Nonempty Act]
    (M : MDC S Act) (hA : ∀ i, M.A i = Finset.univ) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ f : StationaryPolicy M, ∀ θ : Policy M, ∀ i : S,
      discCost f.toPolicy α i ≤ discCost θ α i := by sorry

end DermanSeqDecisions.Stationary
