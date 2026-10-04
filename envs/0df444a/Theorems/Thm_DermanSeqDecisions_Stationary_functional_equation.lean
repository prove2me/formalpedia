-- Prove2me | Theorems.Thm_DermanSeqDecisions_Stationary_functional_equation
-- name    : DermanSeqDecisions.Stationary.functional_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:44:34.248968+00:00
-- url     : https://prove2.me/theorems/65b08095-61fc-449b-919a-f0e2807bf186
-- title:
--   Functional equation of the discounted problem: $V_i = \min_{D_i} \sum_k D_{ik}(w_{ik} + \alpha \sum_j q_{ij}(k) V_j)$
-- statement:
--   Let the states $i, j$ range over a finite set (Derman's $0, \dots, L$) and the decisions $k$ over a finite set (Derman's $d_1, \dots, d_K$), every decision being available in every state. Let $q_{ij}(k) \ge 0$ with $\sum_j q_{ij}(k) = 1$ be the transition probabilities and $w_{ik} \ge 0$ the costs. For a procedure $R$ (history-dependent and randomized, Derman's class $C$) and a discount factor $0 < \alpha < 1$ write
--   $$V_R(i, \alpha) = \sum_{t=0}^{\infty} \alpha^t W_t,$$
--   where $W_t$ is the expected cost at time $t$ when $X_0 = i$, and let $V_i = \min_{R \in C} V_R(i, \alpha)$ be the optimal discounted cost.
--
--   Then for every state $i$,
--   $$V_i = \min_{D_i} \Big\{ \sum_{k} D_{ik} \Big( w_{ik} + \alpha \sum_{j} q_{ij}(k) V_j \Big) \Big\},$$
--   where the minimum runs over all randomizations $D_i = (D_{i1}, \dots, D_{iK})$ with $D_{ik} \ge 0$ and $\sum_k D_{ik} = 1$, and is attained.
--
--   This is the functional equation from which Derman reads off that the discount-optimal procedure can be taken stationary and deterministic: the right-hand side is linear in $D_i$, so a vertex of the simplex attains it.
--
--   **Formalization Note** $V_i$ is the infimum `discValue M α i` of `discCost θ α i` over all policies, in $[0, \infty]$; the randomization is a function to $[0, \infty]$ summing to $1$. "Minimum attained" is stated as `IsLeast`. The costs are only assumed nonnegative, which covers both Problem 1 ($w_{ik} > 0$) and Problem 2 ($w_{Lk} = 0$), for which the proof uses the equation alike.
-- source:
--   Derman, On Sequential Decisions and Markov Chains, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, p. 19, §2, proof of Theorem 1 (unnumbered display)

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_SennottDP_AvgFinite_Criteria

open scoped ENNReal NNReal
open SennottDP.AvgFinite

namespace DermanSeqDecisions.Stationary

/-- The functional equation of the discounted problem (Derman, *On Sequential Decisions and Markov
Chains*, Management Science 9(1):16–24 (1962), DOI 10.1287/mnsc.9.1.16, §2, proof of Theorem 1,
p. 19, unnumbered display). States `S` (Derman's `0, …, L`) and decisions `Act` (Derman's
`d_1, …, d_K`) are finite, every decision is available in every state, `M.P i k j = q_ij(k)` and
`M.C i k = w_ik ≥ 0`. For `0 < α < 1` let `V_i = min_{R ∈ C} V_R(i, α)` be the optimal discounted
cost over all history-dependent randomized procedures. Then `V_i` is the minimum, over all
randomizations `D_i = (D_i1, …, D_iK)` (`D_ik ≥ 0`, `∑_k D_ik = 1`), of
`∑_k D_ik (w_ik + α ∑_j q_ij(k) V_j)`; in particular the minimum is attained.

**Formalization Note.** `V_i` is `discValue M α i`, the infimum of `discCost θ α i` over all
`θ : Policy M` (Derman's class `C`), valued in `[0, ∞]`. The randomization `D_i` is a function
`Act → [0, ∞]` summing to `1` (so each `D_ik ∈ [0, 1]`). "min" is `IsLeast`: the value belongs to
the set of attained right-hand sides and is below each of them. The costs are only assumed
nonnegative: the proof of Theorem 1 uses this equation for Problem 1 (`w_ik > 0`) and for
Problem 2 (`w_Lk = 0`) alike. -/
theorem functional_equation {S : Type*} {Act : Type*} [Fintype S] [Nonempty S]
    [Fintype Act] [Nonempty Act]
    (M : MDC S Act) (hA : ∀ i, M.A i = Finset.univ) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (i : S) :
    IsLeast
      {x : ℝ≥0∞ | ∃ D : Act → ℝ≥0∞, ∑ k, D k = 1 ∧
        x = ∑ k, D k * ((M.C i k : ℝ≥0∞) + ENNReal.ofReal α * ∑ j, M.P i k j * discValue M α j)}
      (discValue M α i) := by sorry

end DermanSeqDecisions.Stationary
