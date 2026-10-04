-- Prove2me | Theorems.Thm_DermanSeqDecisions_Stationary_theorem_1
-- name    : DermanSeqDecisions.Stationary.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:12:37.917756+00:00
-- url     : https://prove2.me/theorems/78b28e9e-3ad7-4c03-aa0c-545adefced86
-- title:
--   Theorem 1 — deterministic stationary procedures are optimal for Problems 1 and 2
-- statement:
--   A system is observed at times $t = 0, 1, \dots$ in one of finitely many states (Derman's $0, \dots, L$). After each observation one of finitely many decisions $d_1, \dots, d_K$ is made, all of them available in every state. In state $i$ under decision $d_k$ the system moves to state $j$ with probability $q_{ij}(k)$ and a cost $w_{ik} \ge 0$ is incurred. A **procedure** $R$ chooses the decision at time $t$ at random, with probabilities that may depend on the whole history $X_0, \Delta_0, \dots, X_t$; $C$ is the class of all procedures and $C''$ the class of **deterministic stationary** procedures, which use a fixed decision $f(i)$ in state $i$ at every time. With $X_0 = i$, write $W_t$ for the expected cost at time $t$,
--   $$Q_R(i) = \limsup_{T \to \infty} \frac{1}{T} \sum_{t=0}^{T} W_t, \qquad S_R(i) = \sum_{t=0}^{\infty} W_t \in [0, \infty].$$
--
--   1. **Problem 1.** If $w_{ik} > 0$ for all $i$ and $k$, there is $R_1 \in C''$ such that
--   $$Q_{R_1}(i) = \min_{R \in C} Q_R(i), \qquad \text{for every state } i.$$
--   2. **Problem 2.** If a state $L$ is absorbing under every decision ($q_{LL}(k) = 1$ for all $k$), $w_{Lk} = 0$ for all $k$ and $w_{ik} > 0$ for $i \ne L$, there is $R_2 \in C''$ such that
--   $$S_{R_2}(i) = \min_{R \in C} S_R(i) \quad (\text{possibly } \infty), \qquad \text{for every state } i.$$
--
--   In both cases one procedure is optimal for every initial state, and it is optimal against all history-dependent randomized procedures, not only against stationary ones. This justifies restricting the search for optimal procedures to the finite class $C''$, as the linear programming formulations of the rest of the paper do.
--
--   **Formalization Note** $Q_R(i)$ is the published `avgCost θ i` $= \limsup_n \frac1n \sum_{t<n} W_t$, which equals Derman's normalization because $W_t$ is bounded by $\max w_{ik}$. $S_R(i)$ is `totalCost θ i` in $[0, \infty]$. "Minimum attained by $R_1$" is $Q_{R_1}(i) \le Q_R(i)$ for every procedure $R$ and state $i$. The page states $w_{ik} > 0$ for all $i$ and also $w_{Lk} = 0$ in Problem 2; Problem 2 is read with $w_{ik} > 0$ for $i \ne L$, and each problem carries its own cost hypotheses.
-- source:
--   Derman, On Sequential Decisions and Markov Chains, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, p. 18, Theorem 1 ((1) and (2)); Problems 1 and 2, p. 17

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_SennottDP_AvgFinite_Criteria
import Definitions.Def_DermanSeqDecisions_Stationary_totalCost

open scoped ENNReal NNReal
open SennottDP.AvgFinite

namespace DermanSeqDecisions.Stationary

/-- Theorem 1 (Derman, *On Sequential Decisions and Markov Chains*, Management Science
9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §2, p. 18, Theorem 1, (1) and (2)). States `S`
(Derman's `0, …, L`) and decisions `Act` (Derman's `d_1, …, d_K`) are finite, every decision is
available in every state, `M.P i k j = q_ij(k)` and `M.C i k = w_ik`.

1. (Problem 1) If `w_ik > 0` for all `i, k`, there is a deterministic stationary procedure
   `R₁ ∈ C″` with `Q_{R₁}(i) = min_{R ∈ C} Q_R(i)` for every `i`.
2. (Problem 2) If a state `L` is absorbing under every decision, `w_Lk = 0` for all `k`, and
   `w_ik > 0` for `i ≠ L`, there is a deterministic stationary procedure `R₂ ∈ C″` with
   `S_{R₂}(i) = min_{R ∈ C} S_R(i)` (possibly `∞`) for every `i`.

**Formalization Note.** `C` is `Policy M` (all history-dependent randomized procedures) and `C″`
is `StationaryPolicy M` via `.toPolicy`; "min attained by `R₁`" is `Q_{R₁}(i) ≤ Q_R(i)` for every
`R` and `i`, with one `R₁` for all initial states. `Q_R(i)` is `avgCost θ i =
limsup_n (∑_{t<n} W_t)/n`; Derman's `limsup_T (1/T) ∑_{t=0}^T W_t` has the same value because
`W_t` is bounded by `max w_ik`. `S_R(i)` is `totalCost θ i ∈ [0, ∞]`. "L absorbing for all
`R ∈ C`" is `M.P L a L = 1` for every decision `a`, as every decision is used by some procedure.
Derman states `w_ik > 0` for all `i` and also `w_Lk = 0`; Problem 2 is read with `w_ik > 0` only
for `i ≠ L`. The two problems carry their own cost hypotheses, in separate implications. -/
theorem theorem_1 {S : Type*} {Act : Type*} [Fintype S] [Nonempty S]
    [Fintype Act] [Nonempty Act]
    (M : MDC S Act) (hA : ∀ i, M.A i = Finset.univ) :
    ((∀ i a, 0 < M.C i a) →
      ∃ R₁ : StationaryPolicy M, ∀ θ : Policy M, ∀ i : S,
        avgCost R₁.toPolicy i ≤ avgCost θ i) ∧
    (∀ L : S, (∀ a, M.P L a L = 1) → (∀ a, M.C L a = 0) → (∀ i a, i ≠ L → 0 < M.C i a) →
      ∃ R₂ : StationaryPolicy M, ∀ θ : Policy M, ∀ i : S,
        totalCost R₂.toPolicy i ≤ totalCost θ i) := by sorry

end DermanSeqDecisions.Stationary
