-- Prove2me | Theorems.Thm_DynRiskEq_Welfare_theorem_3_iv_maximizer
-- name    : DynRiskEq.Welfare.theorem_3_iv_maximizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:41.224992+00:00
-- url     : https://prove2.me/theorems/d24f31d7-5640-4d46-bb7d-cc933444a89c
-- title:
--   Proof of Theorem 3(iv), p. 16 — [μ̄]_{n+} maximizes Σ_m μ(m)(Σ_a C_a(ū_a(m)) + θ̄(m)) over the social risk set D_s(n)
-- statement:
--   Suppose every agent's risk generators are probability vectors on the children of their node, and let $(\bar\pi,\bar\alpha,\bar\mu)$ with actions $(\bar u,\bar x,\bar W,\bar\theta_a)$ be a multistage risk-trading equilibrium RTE$(\mathcal D_{\mathcal A})$, with $\bar\theta=\sum_a\bar\theta_a$. Then for every non-leaf node $n$, $[\bar\mu]_{n_+}\in\mathcal D_s(n)$ and it solves
--   $$\sup_{\mu\in\mathcal D_s(n)}\ \sum_{m\in n_+}\mu(m)\Big(\sum_{a\in\mathcal A}C_a(\bar u_a(m))+\bar\theta(m)\Big),$$
--   that is, $\sum_{m\in n_+}\nu(m)\big(\sum_aC_a(\bar u_a(m))+\bar\theta(m)\big)\le\sum_{m\in n_+}\bar\mu(m)\big(\sum_aC_a(\bar u_a(m))+\bar\theta(m)\big)$ for every $\nu\in\mathcal D_s(n)$.
--
--   The equilibrium security prices are a worst-case measure of the social planner's one-step risk, which is what lets the equilibrium be read as a solution of the social planning system.
--
--   **Formalization Note.** The maximum is stated explicitly (membership plus an upper bound) rather than through a real supremum. The probability hypothesis enters through nonnegativity of the elements of $\mathcal D_s(n)$. Assumption 3 is not needed, because $[\bar\mu]_{n_+}\in\mathcal D_s(n)$ follows from the equilibrium.
-- source:
--   Ferris & Philpott, Dynamic risked equilibrium, author's manuscript of April 16, 2018 (Oper. Res. 2022, doi:10.1287/opre.2019.1958), p. 16, proof of Theorem 3(iv) ("Hence equality holds throughout and thus [μ̄]_{n+} solves …")

import Mathlib
import Definitions.Def_DynRiskEq_Welfare_Model

open StochasticProg.Multistage FirstOrderOpt.ConvexTheory
open scoped RealInnerProductSpace

namespace DynRiskEq.Welfare

/-- Proof of Theorem 3(iv) (p. 16). With probability-vector generators, in a multistage
risk-trading equilibrium `[μ̄]_{n+}` solves `sup_{μ ∈ 𝒟_s(n)} Σ_{m ∈ n+} μ(m)(Σ_a C_a(ū_a(m)) + θ̄(m))`
at every non-leaf node `n`. -/
theorem theorem_3_iv_maximizer {H : ℕ} (T : Tree H) {A : Type} [Fintype A] [DecidableEq A]
    (M : Market T A) (Ka : A → T.Node → ℕ)
    (pa : (a : A) → (n : T.Node) → Fin (Ka a n) → T.Node → ℝ)
    (hprob : ∀ a, ProbGenerators T (Ka a) (pa a))
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ)
    (hRTE : IsRTE T M Ka pa π α μ u x W θa) :
    ∀ n, ¬ IsLeaf T n →
      restrictChildren T μ n ∈ socialRiskSet T Ka pa n ∧
      ∀ ν ∈ socialRiskSet T Ka pa n,
        ∑ m : ↥(T.children n), ν m * (∑ a, M.C a (u a m) + thetaBar T θa m) ≤
          ∑ m ∈ T.children n, μ m * (∑ a, M.C a (u a m) + thetaBar T θa m) := by sorry

end DynRiskEq.Welfare
