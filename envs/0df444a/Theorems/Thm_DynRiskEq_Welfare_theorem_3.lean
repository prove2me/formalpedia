-- Prove2me | Theorems.Thm_DynRiskEq_Welfare_theorem_3
-- name    : DynRiskEq.Welfare.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:50.369087+00:00
-- url     : https://prove2.me/theorems/716734fd-0f24-4bc6-b10d-8b602166dc2b
-- title:
--   Theorem 3, pp. 14–15 — every multistage risk-trading equilibrium prices in every risk set, obeys (24), and solves SE({μ̄}) and SE(D_s)
-- statement:
--   This is the paper's First Welfare Theorem.
--
--   Consider agents $a\in\mathcal A$ on a finite scenario tree, each with polyhedral node-dependent risk sets $\mathcal D_a(n)=\operatorname{conv}\{[p^k_a]_{n_+}\}$, $n\notin\mathcal L$, whose generators are probability vectors on $n_+$, and satisfying Assumption 3: $\bigcap_a\mathcal D_a(n)\neq\emptyset$ for $n\notin\mathcal L$. Let $p^k_s(n)$, $k\in\mathcal K_s(n)$, be generators of the social planning risk set: $\operatorname{conv}\{[p^k_s]_{n_+}\}=\mathcal D_s(n)$ for every $n\notin\mathcal L$. Suppose $\{\bar\pi(n)\}$, $\{\bar\alpha_a(n)\}$, $\{\bar\mu(n)\}$ form a multistage risk-trading equilibrium RTE$(\mathcal D_{\mathcal A})$ in which agent $a$ solves $\mathrm{AE}_a(\bar\pi,\bar\alpha,\bar\mu,\mathcal D_a)$ with policy $(\bar u_a,\bar x_a,\bar\theta_a)$ and security holdings $\bar W_a$. Let $\bar\theta(n)=\sum_a\bar\theta_a(n)$. Then:
--
--   1. $[\bar\mu]_{n_+}\in\mathcal D_a(n)$ for all $a$, and hence $[\bar\mu]_{n_+}\in\mathcal D_s(n)$, for every $n\notin\mathcal L$;
--   2. for every $n\notin\mathcal L$,
--   $$\bar\theta(n)=\sum_{m\in n_+}\bar\mu(m)\Big(\sum_{a\in\mathcal A}C_a(\bar u_a(m))+\bar\theta(m)\Big);\tag{24}$$
--   3. there exist multipliers $\gamma$ such that $(\bar u,\bar x,\bar\theta,\gamma,\bar\pi,\bar\alpha)$ solves SE$(\mathcal D_0)$ with $\mathcal D_0=\{\bar\mu\}$, and $\bar\mu(m)=\gamma^1(n)\bar\mu(m)$ on $n_+$;
--   4. there exist multipliers $\gamma$ such that $(\bar u,\bar x,\bar\theta,\gamma,\bar\pi,\bar\alpha)$ solves SE$(\mathcal D_s)$ and $\bar\mu(m)=\sum_{k\in\mathcal K_s(n)}\gamma^k(n)p^k_s(m)$ for $m\in n_+$, $n\notin\mathcal L$.
--
--   In words: a competitive market in which risk-averse agents trade Arrow–Debreu securities reaches an outcome that a risk-averse social planner, using the intersection of the agents' risk sets, would choose; and the security prices are the planner's worst-case measure.
--
--   **Formalization Note.** The paper's closing clause "$\bar\mu(n)=\sum_{k\in K_s(n)}\gamma^k(n)p^k_a(m)$" mixes $n$ and $m$ and agent and social generators; it is read as the link $\bar\mu(m)=\sum_k\gamma^k(n)p^k_s(m)$ between the multipliers of SE$(\mathcal D_s)$ and the equilibrium price, and posed as part of the conclusion of (iv) (and, trivially, of (iii)). The social generating family is a hypothesis (any finite family whose hull is $\bigcap_a\mathcal D_a(n)$; such a family exists since an intersection of polytopes is a polytope). Note that the printed proof of (iv) obtains $\gamma$ from Lemma 1, which in general yields a single maximizing generator; the multipliers asserted here represent $\bar\mu$ as a convex combination of social generators. Assumption 3 is stated as printed although it follows from (i). Convexity of $C_a$, Assumptions 1, 2 and 4 and equal leaf depth are not assumed: Theorem 3 does not use them. Risk-set generators are probability vectors (risk sets are sets of probability measures, p. 3). Stationarity "$0\in\nabla f(v)+N_S(v)$" requires the gradient to exist and $v\in S$. Vector complementarity is componentwise; $x_a(0_-)$ is given initial storage.
-- source:
--   Ferris & Philpott, Dynamic risked equilibrium, author's manuscript of April 16, 2018 (Oper. Res. 2022, doi:10.1287/opre.2019.1958), pp. 14–15, Theorem 3; proof pp. 15–16

import Mathlib
import Definitions.Def_DynRiskEq_Welfare_Model

open StochasticProg.Multistage FirstOrderOpt.ConvexTheory
open scoped RealInnerProductSpace

namespace DynRiskEq.Welfare

/-- Theorem 3 (pp. 14–15), the First Welfare Theorem. Agents with polyhedral risk sets
(probability-vector generators) satisfying Assumption 3, and a social generating family `(Ks, ps)`
whose convex hull is `𝒟_s(n)` at every non-leaf node. Every multistage risk-trading equilibrium
`(π̄, ᾱ, μ̄; ū, x̄, W̄, θ̄_a)` satisfies (i) `μ̄ ∈ 𝒟_a(n)` for all `a` and `μ̄ ∈ 𝒟_s(n)`; (ii) (24);
(iii) `(ū, x̄, θ̄, γ, π̄, ᾱ)` solves `SE({μ̄})` for some `γ`; (iv) `(ū, x̄, θ̄, γ, π̄, ᾱ)` solves
`SE(𝒟_s)` for some `γ` with `μ̄(m) = Σ_k γ^k(n) p^k_s(m)` on `n+`. -/
theorem theorem_3 {H : ℕ} (T : Tree H) {A : Type} [Fintype A] [DecidableEq A]
    (M : Market T A) (Ka : A → T.Node → ℕ)
    (pa : (a : A) → (n : T.Node) → Fin (Ka a n) → T.Node → ℝ)
    (hprob : ∀ a, ProbGenerators T (Ka a) (pa a))
    (hA3 : ∀ n, ¬ IsLeaf T n → (socialRiskSet T Ka pa n).Nonempty)
    (Ks : T.Node → ℕ) (ps : (n : T.Node) → Fin (Ks n) → T.Node → ℝ)
    (hs : ∀ n, ¬ IsLeaf T n → riskSet T Ks ps n = socialRiskSet T Ka pa n)
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ)
    (hRTE : IsRTE T M Ka pa π α μ u x W θa) :
    -- (i)
    (∀ n, ¬ IsLeaf T n →
      (∀ a, InRisk T (Ka a) (pa a) n μ) ∧ restrictChildren T μ n ∈ socialRiskSet T Ka pa n) ∧
    -- (ii), (24)
    (∀ n, ¬ IsLeaf T n →
      thetaBar T θa n = ∑ m ∈ T.children n, μ m * (∑ a, M.C a (u a m) + thetaBar T θa m)) ∧
    -- (iii), SE(𝒟₀) with 𝒟₀ = {μ̄}: one generator p¹₀ = μ̄ at every node
    (∃ γ : (n : T.Node) → Fin 1 → ℝ,
      SE T M (fun _ => 1) (fun _ _ => μ) u x (thetaBar T θa) γ π α ∧
      ∀ n, ¬ IsLeaf T n → ∀ m ∈ T.children n, μ m = ∑ k, γ n k * μ m) ∧
    -- (iv), SE(𝒟_s), with the closing clause μ̄(m) = Σ_k γ^k(n) p^k_s(m)
    (∃ γ : (n : T.Node) → Fin (Ks n) → ℝ,
      SE T M Ks ps u x (thetaBar T θa) γ π α ∧
      ∀ n, ¬ IsLeaf T n → ∀ m ∈ T.children n, μ m = ∑ k, γ n k * ps n k m) := by sorry

end DynRiskEq.Welfare
