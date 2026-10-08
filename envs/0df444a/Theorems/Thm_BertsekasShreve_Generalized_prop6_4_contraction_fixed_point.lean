-- Prove2me | Theorems.Thm_BertsekasShreve_Generalized_prop6_4_contraction_fixed_point
-- name    : BertsekasShreve.Generalized.prop6_4_contraction_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:55:56.208998+00:00
-- url     : https://prove2.me/theorems/cf305d42-fe8b-477d-ac36-e0816564f60d
-- title:
--   Proposition 6.4 — under A.1–A.5 and $\tilde C$, $J^*$ is the unique fixed point of $T$ in $\bar B\cap F^*$
-- statement:
--   Consider the generalized abstract model of Section 6.1 under conditions A.1–A.5 and Assumption $\tilde C$, with the closed set $\bar B\subseteq B$ and the scalars $m,\rho,\alpha$ of $\tilde C$. Then:
--
--   1. $J^*\in\bar B\cap F^*$ and $J^*$ is the unique fixed point of $T$ within $\bar B\cap F^*$. Furthermore, if $J'\in\bar B\cap F^*$ satisfies $T(J')\le J'$ then $J^*\le J'$, while if $J'\le T(J')$ then $J'\le J^*$.
--   2. For every $\mu\in\tilde M$, $J_\mu\in\bar B\cap\tilde F$ and $J_\mu$ is the unique fixed point of $T_\mu$ within $\bar B\cap\tilde F$.
--   3. $$\lim_{N\to\infty}\|T^N(J)-J^*\|=0\quad\forall J\in\bar B\cap F^*,\qquad\lim_{N\to\infty}\|T_\mu^N(J)-J_\mu\|=0\quad\forall J\in\bar B\cap\tilde F,\ \mu\in\tilde M.$$
--   4. A stationary policy $\pi^*=(\mu^*,\mu^*,\dots)\in\tilde\Pi$ is optimal if and only if $T_{\mu^*}(J^*)=T(J^*)$. Equivalently, $\pi^*$ is optimal if and only if $J_{\mu^*}\in\bar B\cap F^*$ and $T_{\mu^*}(J_{\mu^*})=T(J_{\mu^*})$.
--   5. For every $\varepsilon>0$ there is a stationary policy $\pi_\varepsilon=(\mu_\varepsilon,\mu_\varepsilon,\dots)\in\tilde\Pi$ with $\|J^*-J_{\mu_\varepsilon}\|\le\varepsilon$.
--
--   This is the restricted-class analogue of Propositions 4.2 and 4.3: under a contraction assumption the optimal cost over $\tilde\Pi$ solves Bellman's equation, value iteration converges in sup norm, optimal stationary policies are characterized by Bellman's equation, and $\varepsilon$-optimal stationary policies exist within the restricted class. The book states it without proof.
--
--   **Formalization Note** "$J\in\bar B\cap G$" means $J$ is (the extended-real image of) a bounded real function in $\bar B$ belonging to $G$. A sup-norm bound $\|G-G'\|\le c$ between extended-real functions means both are real at every point and $|G(x)-G'(x)|\le c$ for all $x$; the limits in item 3 are stated as "for every $\varepsilon>0$ the distance is eventually at most $\varepsilon$".
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 97, Proposition 6.4

import Mathlib
import Definitions.Def_BertsekasShreve_Generalized_Model
import Definitions.Def_BertsekasShreve_Generalized_Assumptions
import Definitions.Def_BertsekasShreve_Generalized_Optimality

namespace BertsekasShreve.Generalized

open Filter Topology

/-- Proposition 6.4, p. 97. Let A.1–A.5 and Assumption C̃ hold, with the closed set `B̄ ⊆ B` and
the scalars `m`, `ρ`, `α` of C̃.
(a) `J* ∈ B̄ ∩ F*` and `J*` is the unique fixed point of `T` within `B̄ ∩ F*`; if `J' ∈ B̄ ∩ F*`
and `T(J') ≤ J'` then `J* ≤ J'`, while if `J' ≤ T(J')` then `J' ≤ J*`.
(b) For every `μ ∈ M̃`, `J_μ ∈ B̄ ∩ F̃` and `J_μ` is the unique fixed point of `T_μ` within
`B̄ ∩ F̃`.
(c) `‖T^N(J) − J*‖ → 0` for all `J ∈ B̄ ∩ F*`, and `‖T_μ^N(J) − J_μ‖ → 0` for all `J ∈ B̄ ∩ F̃`,
`μ ∈ M̃`.
(d) A stationary policy `(μ*, μ*, …) ∈ Π̃` is optimal iff `T_{μ*}(J*) = T(J*)`; equivalently,
iff `J_{μ*} ∈ B̄ ∩ F*` and `T_{μ*}(J_{μ*}) = T(J_{μ*})`.
(e) For every `ε > 0` there is a stationary `(μ_ε, μ_ε, …) ∈ Π̃` with `‖J* − J_{μ_ε}‖ ≤ ε`.

The sup-norm statements are written with `SupDistLe`: `‖G − G'‖ ≤ c` means `G`, `G'` are real at
every point and `|G(x) − G'(x)| ≤ c` for all `x`; convergence in (c) is "for every `ε > 0` the
distance is eventually `≤ ε`". -/
theorem prop6_4_contraction_fixed_point {S C : Type*} (P : Model S C)
    (hA1 : P.A1) (hA2 : P.A2) (hA3 : P.A3) (hA4 : P.A4) (hA5 : P.A5)
    (Bbar : Set (BertsekasShreve.Contraction.BFun S)) (m : ℕ) (ρ α : ℝ) (hC : P.AssumptionCtilde Bbar m ρ α) :
    -- (a)
    (MemBbarInter Bbar P.Fstar P.Jstar ∧ P.T P.Jstar = P.Jstar ∧
      (∀ J', MemBbarInter Bbar P.Fstar J' → P.T J' = J' → J' = P.Jstar) ∧
      (∀ J', MemBbarInter Bbar P.Fstar J' → P.T J' ≤ J' → P.Jstar ≤ J') ∧
      (∀ J', MemBbarInter Bbar P.Fstar J' → J' ≤ P.T J' → J' ≤ P.Jstar)) ∧
    -- (b)
    (∀ μ : P.Sel, MemBbarInter Bbar P.Ftil (P.Jmu μ) ∧ P.Tmu μ.1 (P.Jmu μ) = P.Jmu μ ∧
      ∀ J', MemBbarInter Bbar P.Ftil J' → P.Tmu μ.1 J' = J' → J' = P.Jmu μ) ∧
    -- (c)
    (∀ J, MemBbarInter Bbar P.Fstar J → ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → BertsekasShreve.Contraction.SupDistLe (P.T^[N] J) P.Jstar ε) ∧
    (∀ μ : P.Sel, ∀ J, MemBbarInter Bbar P.Ftil J → ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → BertsekasShreve.Contraction.SupDistLe ((P.Tmu μ.1)^[N] J) (P.Jmu μ) ε) ∧
    -- (d)
    (∀ μ : P.Sel,
      (P.IsOptimal (P.stationary μ) ↔ P.Tmu μ.1 P.Jstar = P.T P.Jstar) ∧
      (P.IsOptimal (P.stationary μ) ↔
        MemBbarInter Bbar P.Fstar (P.Jmu μ) ∧ P.Tmu μ.1 (P.Jmu μ) = P.T (P.Jmu μ))) ∧
    -- (e)
    (∀ ε : ℝ, 0 < ε → ∃ μ : P.Sel, BertsekasShreve.Contraction.SupDistLe P.Jstar (P.Jmu μ) ε) := by sorry

end BertsekasShreve.Generalized
