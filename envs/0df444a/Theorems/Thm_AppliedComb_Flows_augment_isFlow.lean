-- Prove2me | Theorems.Thm_AppliedComb_Flows_augment_isFlow
-- name    : AppliedComb.Flows.augment_isFlow
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:40:00.732239+00:00
-- url     : https://prove2.me/theorems/1e4726f6-fd32-499c-98a6-0bd71c0f55ef
-- title:
--   Proposition 13.7 — augmenting along a path gives a flow of value v + δ
-- statement:
--   Let $\phi$ be a flow of value $v$ in a network, and let $P = (x_0, x_1, \dots, x_m)$ be an augmenting path for $\phi$, with $\delta$ calculated as in Section 13.3: $\delta = \delta_1$ if $P$ has no backward edge and $\delta = \min\{\delta_1, \delta_2\}$ otherwise. Modify $\phi$ by increasing the flow along the forward edges of $P$ by $\delta$ and decreasing the flow along the backward edges of $P$ by $\delta$. Then the resulting function $\hat\phi$ is a flow and
--   $$\operatorname{value}(\hat\phi) = v + \delta.$$
--
--   This is the improvement step of the Ford–Fulkerson labeling algorithm. The book leaves its proof as an exercise (Exercise 13.7.4).
--
--   **Formalization Note.** The hypothesis "$\delta$ calculated as above" is the equation `N.delta ϕ x = (δ : WithTop ℝ)` between the `WithTop ℝ`-valued $\min\{\delta_1, \delta_2\}$ of `AppliedComb.Flows.AugmentingPath` and the real number $\delta$; it pins $\delta$ down uniquely, and for every augmenting path such a real $\delta$ exists. The positivity $\delta > 0$ is not assumed: it is a consequence of the definitions.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 265, Proposition 13.7 (with δ as defined on pp. 264–265)

import Mathlib
import Definitions.Def_AppliedComb_Flows_Network
import Definitions.Def_AppliedComb_Flows_AugmentingPath

namespace AppliedComb.Flows

/-- **Proposition 13.7** (Keller & Trotter, *Applied Combinatorics*, 2017 Edition, p. 265). Let
`ϕ` be a flow of value `v` in the network `N` and let `P = (x₀, x₁, …, xₘ)` be an augmenting path
for `ϕ`, with `δ` calculated as on pp. 264–265 (`δ = δ₁` if `P` has no backward edge, otherwise
`δ = min {δ₁, δ₂}`). Increase the flow along the forward edges of `P` by `δ` and decrease it
along the backward edges of `P` by `δ`. Then the resulting function `ϕ̂` is a flow and it has
value `v + δ`. -/
theorem augment_isFlow {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ϕ : V → V → ℝ) (hϕ : N.IsFlow ϕ)
    {m : ℕ} (x : Fin (m + 1) → V) (hP : N.IsAugmentingPath ϕ x)
    (δ : ℝ) (hδ : N.delta ϕ x = (δ : WithTop ℝ)) :
    N.IsFlow (N.augment ϕ x δ) ∧ N.value (N.augment ϕ x δ) = N.value ϕ + δ := by sorry

end AppliedComb.Flows
