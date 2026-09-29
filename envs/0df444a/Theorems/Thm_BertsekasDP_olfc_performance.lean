-- Prove2me | Theorems.Thm_BertsekasDP_olfc_performance
-- name    : BertsekasDP.olfc_performance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-11T01:48:56.697652+00:00
-- url     : https://prove2.me/theorems/181044d2-f9bb-43d8-ab30-c8962a0b1158
-- title:
--   OLFC beats open-loop control (Prop. 6.2.1)
-- statement:
--   **Proposition 6.2.1 (the open-loop feedback controller uses measurements advantageously).** Consider the basic stochastic model with state-independent control constraint sets, in the perfect state information case. The **open-loop feedback controller** (OLFC) $\bar\pi$ acts as follows: at stage $k$ in state $x$, it solves the open-loop problem over the remaining horizon starting from $x$ — optimizing over control *sequences*, as if no further measurements were to be received — and applies the first control of an optimal such sequence. Then for every initial state $x_0$,
--
--   $$J_{\bar\pi}(x_0) \;\le\; J_u(x_0) \qquad \text{for every admissible open-loop control sequence } u = (u_0, \dots, u_{N-1}).$$
--
--   That is, the closed-loop cost of the OLFC is at most the cost of the best fixed control sequence.
--
--   The point is that a suboptimal scheme should at least not waste the information it receives. The OLFC selects each control as if the future were unobservable, yet because it re-optimizes at every stage from the state actually reached, it dominates every policy that ignores observations altogether. This guarantee is what distinguishes it from the certainty equivalent controller, which, as the source notes, can be strictly worse than the optimal open-loop policy.
--
--   **Formalization Note** The constraint sets are assumed independent of the state, matching the open-loop framework of §6.2 in which a single sequence must be feasible along all trajectories. The OLFC is characterized by a hypothesis — at each stage and state there exists an optimal admissible sequence whose first control the policy plays — rather than constructed, so the statement is about any policy with that property. The perfect-information case is the one formalized here; the source's general version additionally propagates the conditional state distribution.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Proposition 6.2.1 (perfect-information form)

import Mathlib
import Definitions.Def_BertsekasDPModel
import Definitions.Def_BertsekasDPOpenLoopCost

namespace BertsekasDP

theorem olfc_performance {S C W : Type} [Fintype W]
    (M : BertsekasDPModel S C W)
    (hUconst : ∀ k x x', M.U k x = M.U k x')
    (π : ℕ → S → C)
    (holfc : ∀ k, k < M.N → ∀ x, ∃ useq : ℕ → C,
      (∀ i, k ≤ i → i < M.N → useq i ∈ M.U i x) ∧
      π k x = useq k ∧
      (∀ useq' : ℕ → C, (∀ i, k ≤ i → i < M.N → useq' i ∈ M.U i x) →
        BertsekasDPOpenLoopCost M useq (M.N - k) x ≤
          BertsekasDPOpenLoopCost M useq' (M.N - k) x)) :
    ∀ (x₀ : S) (useq₀ : ℕ → C), (∀ i, i < M.N → useq₀ i ∈ M.U i x₀) →
      BertsekasDPPolicyCost M π M.N x₀ ≤
        BertsekasDPOpenLoopCost M useq₀ M.N x₀ := by sorry

end BertsekasDP
