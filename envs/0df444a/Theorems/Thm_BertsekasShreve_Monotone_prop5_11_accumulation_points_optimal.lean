-- Prove2me | Theorems.Thm_BertsekasShreve_Monotone_prop5_11_accumulation_points_optimal
-- name    : BertsekasShreve.Monotone.prop5_11_accumulation_points_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T03:20:36.480254+00:00
-- url     : https://prove2.me/theorems/a3a0f45f-69ff-4bc7-b0ea-7620ab86783f
-- title:
--   Proposition 5.11 — accumulation points of DP-minimizing controls form an optimal stationary policy
-- statement:
--   Consider the abstract monotone dynamic programming model (state space $S$, control space $C$, nonempty constraint sets $U(x)\subseteq C$, monotone mapping $H$, terminal function $J_0>-\infty$), with operators $T_\mu(J)(x)=H(x,\mu(x),J)$ and $T(J)(x)=\inf_{u\in U(x)}H(x,u,J)$, policy costs $J_\pi=\lim_N(T_{\mu_0}\cdots T_{\mu_{N-1}})(J_0)$, stationary costs $J_\mu$ and optimal cost $J^*=\inf_\pi J_\pi$. Assume:
--
--   1. Assumptions I, I.1 and I.2 hold;
--   2. $C$ is a Hausdorff topological space;
--   3. there is a nonnegative integer $\bar k$ such that for each $x\in S$, $\lambda\in\mathbb R$ and $k\ge\bar k$ the set
--   $$U_k(x,\lambda)=\{u\in U(x)\mid H[x,u,T^k(J_0)]\le\lambda\}$$
--   is compact.
--
--   Then:
--
--   (a) There exists a policy $\pi^*=(\mu_0^*,\mu_1^*,\dots)$ attaining the infimum in the DP algorithm for all $k\ge\bar k$:
--   $$(T_{\mu_k^*}T^k)(J_0)=T^{k+1}(J_0)\qquad\forall k\ge\bar k. \tag{43}$$
--
--   (b) For every policy $\pi^*$ satisfying (43), the sequence $\{\mu_k^*(x)\}_{k\ge0}$ has at least one accumulation point in $C$ for each $x\in S$ with $J^*(x)<\infty$.
--
--   (c) Let $\pi^*$ satisfy (43). If $\mu^* : S\to C$ is such that $\mu^*(x)$ is an accumulation point of $\{\mu_k^*(x)\}$ for every $x\in S$ with $J^*(x)<\infty$, and $\mu^*(x)\in U(x)$ for every $x\in S$ with $J^*(x)=\infty$, then $\mu^*(x)\in U(x)$ for all $x$ and the stationary policy $(\mu^*,\mu^*,\dots)$ is optimal:
--   $$J_{\mu^*}=J^*.$$
--
--   The proposition makes the value-iteration algorithm constructive: the controls that attain the minimum at each stage of the DP recursion, followed to an accumulation point state by state, yield an optimal stationary policy.
--
--   **Formalization Note** The model and assumptions are the published `MonotoneDP.Increase` definitions; "I.2 holds" is $\exists\alpha$, `AssumptionI2 α`. An accumulation point of $\{\mu_k^*(x)\}$ is a cluster point of the sequence (`MapClusterPt u atTop`), not a limit. In (c) the admissibility of $\mu^*$ is part of the conclusion, as the existence of a proof that $\mu^*(x)\in U(x)$ for all $x$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 87, Proposition 5.11, Eq. (43) of Chapter 5; hypotheses from p. 86, Proposition 5.10, Eq. (40) of Chapter 5

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace BertsekasShreve.Monotone

open Filter Topology

/-- Bertsekas & Shreve (1996), p. 87, Proposition 5.11, under the assumptions of Proposition 5.10
(p. 86): I, I.1 and I.2 hold, the control space `C` is a Hausdorff space, and for a nonnegative
integer `k̄` the sets `U_k(x, λ) = {u ∈ U(x) | H[x, u, T^k(J₀)] ≤ λ}` (eq. (40)) are compact for all
`x ∈ S`, `λ ∈ ℝ`, `k ≥ k̄`. Then
(a) some policy `π* = (μ₀*, μ₁*, …)` satisfies `(T_{μ_k*} T^k)(J₀) = T^{k+1}(J₀)` for all `k ≥ k̄`
(eq. (43));
(b) for every policy satisfying (43), `{μ_k*(x)}` has an accumulation point whenever
`J*(x) < ∞`;
(c) if `μ* : S → C` takes an accumulation point of `{μ_k*(x)}` at every `x` with `J*(x) < ∞` and a
value in `U(x)` at every `x` with `J*(x) = ∞`, then `μ*` is admissible and the stationary policy
`(μ*, μ*, …)` is optimal. -/
theorem prop5_11_accumulation_points_optimal {S C : Type*} [TopologicalSpace C] [T2Space C]
    (m : MonotoneDP.Increase.Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α)
    (kbar : ℕ)
    (hcpt : ∀ x : S, ∀ lam : ℝ, ∀ k : ℕ, kbar ≤ k →
      IsCompact {u | u ∈ m.U x ∧ m.H x u ((m.T)^[k] m.Jbar) ≤ (lam : EReal)}) :
    (∃ π : m.Policy, ∀ k : ℕ, kbar ≤ k →
        m.Tmu (π k) ((m.T)^[k] m.Jbar) = (m.T)^[k + 1] m.Jbar) ∧
    (∀ π : m.Policy, (∀ k : ℕ, kbar ≤ k →
        m.Tmu (π k) ((m.T)^[k] m.Jbar) = (m.T)^[k + 1] m.Jbar) →
      ∀ x : S, m.Jstar x < ⊤ → ∃ u : C, MapClusterPt u atTop (fun k => (π k).1 x)) ∧
    (∀ π : m.Policy, (∀ k : ℕ, kbar ≤ k →
        m.Tmu (π k) ((m.T)^[k] m.Jbar) = (m.T)^[k + 1] m.Jbar) →
      ∀ μ : S → C,
        (∀ x : S, m.Jstar x < ⊤ → MapClusterPt (μ x) atTop (fun k => (π k).1 x)) →
        (∀ x : S, m.Jstar x = ⊤ → μ x ∈ m.U x) →
        ∃ hμ : ∀ x, μ x ∈ m.U x, m.Jmu ⟨μ, hμ⟩ = m.Jstar) := by sorry

end BertsekasShreve.Monotone
