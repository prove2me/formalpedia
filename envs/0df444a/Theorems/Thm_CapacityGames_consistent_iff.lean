-- Prove2me | Theorems.Thm_CapacityGames_consistent_iff
-- name    : CapacityGames.consistent_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:52.565844+00:00
-- url     : https://prove2.me/theorems/cac11b47-ef18-413f-a811-08e03160e60c
-- title:
--   Consistency (8) is equivalent to (a) $\sum_{j\in S}\Delta_j(t^*_S)=0$ and (b) inequality (9)
-- statement:
--   Let $\{\Delta_j:j\in N\}$ be real functions of the capacity vector. Recall that the family is *consistent with the costs* if for every $S\subseteq N$
--   $$\max\Big\{\Pi_{\mathcal C}(t,s)+\sum_{j\in S}\Delta_j(t): t\in\mathbf T,\ s(D)\in X(t)\ \forall D,\ I(t)\subseteq S\Big\}=\Pi^*_{\mathcal C}(S)\quad(8)$$
--   and the maximum is attained at a supply chain optimal choice $(t^*_S,s^*_S)$ for $S$.
--
--   Then the family is consistent if and only if, for every $S\subseteq N$:
--
--   1. (a) some supply chain optimal choice $(t^*_S,s^*_S)$ for $S$ (feasible, $I(t^*_S)\subseteq S$, $\Pi_{\mathcal C}(t^*_S,s^*_S)=\Pi^*_{\mathcal C}(S)$) has $\sum_{j\in S}\Delta_j(t^*_S)=0$; and
--   2. (b) every feasible choice $(t,s)$ with $I(t)\subseteq S$ satisfies
--   $$\sum_{j\in S}\Delta_j(t)\le\Pi^*_{\mathcal C}(S)-\Pi_{\mathcal C}(t,s).\quad(9)$$
--
--   The proof of Theorem 2 uses consistency only through (a) and (b).
--
--   **Formalization Note** $\Pi^*_{\mathcal C}(S)$ is the supremum of the supply chain values over $I(t)\subseteq S$; no attainment is assumed, since both sides speak of an attaining choice explicitly.
--
--   Differences from the source:
--   - reading: "the maximization is attained at $t^*_S$", with $t^*_S$ "an optimal solution" of (4) → attained at some supply chain optimal choice for $S$, on both sides of the equivalence; reason: the paper does not fix which optimal solution $t^*_S$ is.
--   - reading: expectations taken without comment → integrability of $V(D,s(D))$ and $C_i(s(D))$ is part of feasibility; reason: the paper writes these expectations, which presupposes them.
--   - encoding: $\Delta_j:\mathbf T\to\mathbb R$ → $\Delta_j$ defined on all real vectors; reason: only values on $\mathbf T$ enter, since every feasible $t$ lies in $\mathbf T$.
--   - encoding: $N=\{1,\dots,n\}$ → a finite type $N$, $\Pi^*_{\mathcal C}$ as a supremum; reason: Lean convention, same instances.
-- source:
--   Anderson–Chen–Shao, Capacity Games with Supply Function Competition, arXiv:1905.11084v1, §4, (8) and (9), p.11

import Mathlib
import Definitions.Def_CapacityGames_SetFunction
import Definitions.Def_CapacityGames_Model

open MeasureTheory

namespace CapacityGames

/-- **Two forms of consistency**, arXiv:1905.11084v1, §4, (8) and (9), p.11: a family `Δ` is
consistent with the costs (8) if and only if, for every `S ⊆ N`,
(a) some supply chain optimal choice `(t*_S, s*_S)` for `S` (feasible, `I(t*_S) ⊆ S`,
`Π_C(t*_S, s*_S) = Π*_C(S)`) has `Σ_{j∈S} Δ_j(t*_S) = 0`, and
(b) every choice `(t, s)` feasible for the supply chain with `I(t) ⊆ S` has
`Σ_{j∈S} Δ_j(t) ≤ Π*_C(S) − Π_C(t, s)`. -/
theorem consistent_iff {N Ω : Type*} [Fintype N] [MeasurableSpace Ω]
    (G : CapacityGame N Ω) (hG : G.IsValid) (Δ : N → (N → ℝ) → ℝ) :
    Consistent G Δ ↔ ∀ S : Finset N,
      (∃ p : Choice N Ω, SCFeasible G p ∧ support p.t ⊆ S ∧
          scProfit G p = scOptValue G S ∧ ∑ j ∈ S, Δ j p.t = 0) ∧
      (∀ p : Choice N Ω, SCFeasible G p → support p.t ⊆ S →
          ∑ j ∈ S, Δ j p.t ≤ scOptValue G S - scProfit G p) := by sorry

end CapacityGames
