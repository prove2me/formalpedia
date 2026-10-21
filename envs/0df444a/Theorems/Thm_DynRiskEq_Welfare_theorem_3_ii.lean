-- Prove2me | Theorems.Thm_DynRiskEq_Welfare_theorem_3_ii
-- name    : DynRiskEq.Welfare.theorem_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:39.407983+00:00
-- url     : https://prove2.me/theorems/46a6458d-6fd3-4827-9781-cafe70ac94ed
-- title:
--   Theorem 3(ii), (24), p. 15 — the aggregate value θ̄ = Σ_a θ̄_a obeys the risk-adjusted recursion under μ̄
-- statement:
--   Let $(\bar\pi,\bar\alpha,\bar\mu)$ with actions $(\bar u,\bar x,\bar W,\bar\theta_a)$ be a multistage risk-trading equilibrium RTE$(\mathcal D_{\mathcal A})$, and let $\bar\theta(n)=\sum_{a\in\mathcal A}\bar\theta_a(n)$. Then for every non-leaf node $n$,
--   $$\bar\theta(n)=\sum_{m\in n_+}\bar\mu(m)\Big(\sum_{a\in\mathcal A}C_a(\bar u_a(m))+\bar\theta(m)\Big).\tag{24}$$
--
--   In equilibrium the aggregate risk-adjusted disbenefit is the expectation, under the security prices, of the total cost at the children plus their aggregate value: the payments for products, storage and securities cancel out across agents by market clearing.
--
--   **Formalization Note.** No probability hypothesis on the generators is needed.
-- source:
--   Ferris & Philpott, Dynamic risked equilibrium, author's manuscript of April 16, 2018 (Oper. Res. 2022, doi:10.1287/opre.2019.1958), p. 15, Theorem 3(ii), equation (24)

import Mathlib
import Definitions.Def_DynRiskEq_Welfare_Model

open StochasticProg.Multistage FirstOrderOpt.ConvexTheory
open scoped RealInnerProductSpace

namespace DynRiskEq.Welfare

/-- Theorem 3(ii), (24) (p. 15). In a multistage risk-trading equilibrium,
`θ̄(n) = Σ_{m ∈ n+} μ̄(m)(Σ_a C_a(ū_a(m)) + θ̄(m))` at every non-leaf node, where
`θ̄ = Σ_a θ̄_a`. -/
theorem theorem_3_ii {H : ℕ} (T : Tree H) {A : Type} [Fintype A] [DecidableEq A]
    (M : Market T A) (Ka : A → T.Node → ℕ)
    (pa : (a : A) → (n : T.Node) → Fin (Ka a n) → T.Node → ℝ)
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ)
    (hRTE : IsRTE T M Ka pa π α μ u x W θa) :
    ∀ n, ¬ IsLeaf T n →
      thetaBar T θa n = ∑ m ∈ T.children n, μ m * (∑ a, M.C a (u a m) + thetaBar T θa m) := by sorry

end DynRiskEq.Welfare
