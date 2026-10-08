-- Prove2me | Theorems.Thm_BertsekasShreve_Contraction_compactness_stationary_optimal
-- name    : BertsekasShreve.Contraction.compactness_stationary_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:14:24.167126+00:00
-- url     : https://prove2.me/theorems/05a19cde-3f8e-45c9-9614-b4f79cc22188
-- title:
--   Proposition 4.4 — compact sublevel sets give DP-attaining policies whose accumulation points are optimal
-- statement:
--   Let Assumption C hold and let the control space $C$ be a Hausdorff topological space. Assume that for some $\bar J\in\bar B$ and some positive integer $\bar k$ the sets
--
--   $$U_k(x,\lambda)=\{u\in U(x)\mid H[x,u,T^k(\bar J)]\le\lambda\}$$
--
--   are compact for all $x\in S$, $\lambda\in\mathbb R$ and $k\ge\bar k$. Then:
--
--   1. there exists a policy $\pi^*=(\mu_0^*,\mu_1^*,\dots)\in\Pi$ attaining the infimum in the DP algorithm from $\bar J$ at all $x$ and $k\ge\bar k$, i.e.
--   $$(T_{\mu_k^*}T^k)(\bar J)=T^{k+1}(\bar J)\qquad\forall k\ge\bar k;\qquad(6)$$
--   2. there exists a stationary optimal policy;
--   3. for every policy $\pi^*$ satisfying (6), the sequence $\{\mu_k^*(x)\}$ has at least one accumulation point for each $x\in S$;
--   4. for every policy $\pi^*$ satisfying (6), if $\mu^*:S\to C$ is such that $\mu^*(x)$ is an accumulation point of $\{\mu_k^*(x)\}$ for each $x$, then $\mu^*\in M$ and the stationary policy $(\mu^*,\mu^*,\dots)$ is optimal.
--
--   The proposition shows that stationary optimal policies can be obtained in the limit from the controls the DP algorithm selects at finite horizons.
--
--   **Formalization Note** The book prints $J$ for the fixed initial function in (5)–(6); it is the $\bar J\in\bar B$ of the hypothesis. An accumulation point of $\{\mu_k^*(x)\}$ is a cluster point of the sequence (`MapClusterPt` along `atTop`). Part 4 also asserts $\mu^*(x)\in U(x)$, which the book presupposes when it calls $(\mu^*,\mu^*,\dots)$ a stationary policy.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 57, Proposition 4.4, Eqs. (5)–(6) of Chapter 4

import Mathlib
import Definitions.Def_BertsekasShreve_Contraction_Model
import Definitions.Def_BertsekasShreve_Contraction_AssumptionC

namespace BertsekasShreve.Contraction

open Filter Topology

/-- Proposition 4.4, p. 57. Assume Assumption C, that `C` is a Hausdorff space, and that for some
`J̄ ∈ B̄` and positive integer `k̄` the sets `U_k(x, λ) = {u ∈ U(x) | H[x, u, T^k(J̄)] ≤ λ}` are
compact for all `x ∈ S`, `λ ∈ ℝ`, `k ≥ k̄`. Then
(a) some policy `π* = (μ₀*, μ₁*, …)` satisfies `(T_{μ_k*} T^k)(J̄) = T^{k+1}(J̄)` for all `k ≥ k̄` (6);
(b) there is a stationary optimal policy;
(c) for every `π*` satisfying (6), `{μ_k*(x)}` has an accumulation point for each `x`;
(d) for every `π*` satisfying (6), if `μ*(x)` is an accumulation point of `{μ_k*(x)}` for each
`x`, then `μ* ∈ M` and the stationary policy `(μ*, μ*, …)` is optimal. -/
theorem compactness_stationary_optimal {S C : Type*} [TopologicalSpace C] [T2Space C]
    (P : Model S C) (Bbar : Set (BFun S)) (m : ℕ) (ρ α : ℝ) (hC : AssumptionC P Bbar m ρ α)
    (Jb : BFun S) (hJb : Jb ∈ Bbar) (kb : ℕ) (hkb : 0 < kb)
    (hcompact : ∀ (x : S) (lam : ℝ), ∀ k ≥ kb,
      IsCompact {u : C | u ∈ P.U x ∧ P.H x u (P.T^[k] (toF Jb)) ≤ (lam : EReal)}) :
    (∃ πs : P.Policy, ∀ k ≥ kb, P.Tmu (πs k) (P.T^[k] (toF Jb)) = P.T^[k + 1] (toF Jb)) ∧
    (∃ μs : P.Selector, P.Jmu μs = P.Jstar) ∧
    (∀ πs : P.Policy, (∀ k ≥ kb, P.Tmu (πs k) (P.T^[k] (toF Jb)) = P.T^[k + 1] (toF Jb)) →
      ∀ x : S, ∃ u : C, MapClusterPt u atTop (fun k : ℕ => (πs k).1 x)) ∧
    (∀ πs : P.Policy, (∀ k ≥ kb, P.Tmu (πs k) (P.T^[k] (toF Jb)) = P.T^[k + 1] (toF Jb)) →
      ∀ μs : S → C, (∀ x : S, MapClusterPt (μs x) atTop (fun k : ℕ => (πs k).1 x)) →
        ∃ hμs : ∀ x, μs x ∈ P.U x, P.Jmu ⟨μs, hμs⟩ = P.Jstar) := by sorry

end BertsekasShreve.Contraction
