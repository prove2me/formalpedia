-- Prove2me | Theorems.Thm_BertsekasShreve_Contraction_preliminary_results
-- name    : BertsekasShreve.Contraction.preliminary_results
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:13:59.825974+00:00
-- url     : https://prove2.me/theorems/e343be7a-3256-4873-b939-f3ede9e37534
-- title:
--   Proposition 4.1 — preliminary results under Assumption C
-- statement:
--   Let Assumption C hold for a model with closed set $\bar B$ and scalars $m,\rho,\alpha$. Then:
--
--   1. For every $J\in\bar B$, $\pi=(\mu_0,\mu_1,\dots)\in\Pi$ and $x\in S$,
--   $$J_\pi(x)=\lim_{N\to\infty}(T_{\mu_0}\cdots T_{\mu_{N-1}})(J_0)(x)=\lim_{N\to\infty}(T_{\mu_0}\cdots T_{\mu_{N-1}})(J)(x).$$
--   2. For each positive integer $N$ and each $J\in\bar B$,
--   $$\inf_{\pi\in\Pi}(T_{\mu_0}\cdots T_{\mu_{N-1}})(J)=T^N(J),$$
--   and in particular $J^*_N=\inf_{\pi\in\Pi}(T_{\mu_0}\cdots T_{\mu_{N-1}})(J_0)=T^N(J_0)$.
--   3. For all $J,J'\in\bar B$ and $\mu\in M$,
--   $$\|T^m(J)-T^m(J')\|\le\rho\|J-J'\|,\qquad\|T^m_\mu(J)-T^m_\mu(J')\|\le\rho\|J-J'\|.$$
--
--   Part 1 says that the cost of a policy does not depend on the terminal function within $\bar B$; part 2 says that the finite-horizon problem is solved by the DP algorithm; part 3 is the contraction property to which the Fixed Point Theorem is applied.
--
--   **Formalization Note** "$\|\cdot\|\le c$" for functions in $F=$ `S → EReal` is `SupDistLe`. Infima over $\Pi$ are taken pointwise in `EReal`.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 53, Proposition 4.1

import Mathlib
import Definitions.Def_BertsekasShreve_Contraction_Model
import Definitions.Def_BertsekasShreve_Contraction_AssumptionC

namespace BertsekasShreve.Contraction

open Filter Topology

/-- Proposition 4.1, p. 53. Under Assumption C:
(a) for every `J ∈ B̄` and `π ∈ Π`, `J_π = lim_N (T_{μ₀} ⋯ T_{μ_{N−1}})(J₀) = lim_N (T_{μ₀} ⋯ T_{μ_{N−1}})(J)`
pointwise;
(b) for each positive integer `N` and `J ∈ B̄`, `inf_π (T_{μ₀} ⋯ T_{μ_{N−1}})(J) = T^N(J)`, and
`J*_N = T^N(J₀)`;
(c) `‖T^m(J) − T^m(J')‖ ≤ ρ‖J − J'‖` and `‖T_μ^m(J) − T_μ^m(J')‖ ≤ ρ‖J − J'‖` for `J, J' ∈ B̄`. -/
theorem preliminary_results {S C : Type*} (P : Model S C) (Bbar : Set (BFun S)) (m : ℕ)
    (ρ α : ℝ) (hC : AssumptionC P Bbar m ρ α) :
    (∀ J ∈ Bbar, ∀ (π : P.Policy) (x : S),
      Tendsto (fun N => P.comp π N P.J0 x) atTop (𝓝 (P.Jpi π x)) ∧
      Tendsto (fun N => P.comp π N (toF J) x) atTop (𝓝 (P.Jpi π x))) ∧
    (∀ N : ℕ, 1 ≤ N → ∀ J ∈ Bbar,
      (fun x => ⨅ π : P.Policy, P.comp π N (toF J) x) = P.T^[N] (toF J)) ∧
    (∀ N : ℕ, 1 ≤ N → P.JNstar N = P.T^[N] P.J0) ∧
    (∀ J ∈ Bbar, ∀ J' ∈ Bbar,
      SupDistLe (P.T^[m] (toF J)) (P.T^[m] (toF J')) (ρ * ‖J - J'‖)) ∧
    (∀ μ : P.Selector, ∀ J ∈ Bbar, ∀ J' ∈ Bbar,
      SupDistLe ((P.Tmu μ)^[m] (toF J)) ((P.Tmu μ)^[m] (toF J')) (ρ * ‖J - J'‖)) := by sorry

end BertsekasShreve.Contraction
