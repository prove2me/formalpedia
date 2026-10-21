-- Prove2me | Theorems.Thm_DynRiskEq_Welfare_theorem_3_i
-- name    : DynRiskEq.Welfare.theorem_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:39.669269+00:00
-- url     : https://prove2.me/theorems/c674e798-e5aa-4d51-9025-a6cc19319816
-- title:
--   Theorem 3(i), p. 15 — equilibrium security prices lie in every agent's risk set, hence in the social risk set
-- statement:
--   Let $(\bar\pi,\bar\alpha,\bar\mu)$ with actions $(\bar u,\bar x,\bar W,\bar\theta_a)$ be a multistage risk-trading equilibrium RTE$(\mathcal D_{\mathcal A})$ (Definition 3). Then for every non-leaf node $n$,
--   $$[\bar\mu]_{n_+}\in\mathcal D_a(n)\ \text{ for all } a\in\mathcal A,\qquad\text{hence}\qquad [\bar\mu]_{n_+}\in\mathcal D_s(n)=\bigcap_{a\in\mathcal A}\mathcal D_a(n).$$
--
--   The equilibrium prices of the Arrow–Debreu securities are thus a probability measure every agent regards as admissible: they form a common risk-adjusted measure.
--
--   **Formalization Note.** Membership is about the restriction of $\bar\mu$ to the children of $n$; values of $\bar\mu$ elsewhere play no role. No probability hypothesis on the generators is needed.
-- source:
--   Ferris & Philpott, Dynamic risked equilibrium, author's manuscript of April 16, 2018 (Oper. Res. 2022, doi:10.1287/opre.2019.1958), p. 15, Theorem 3(i)

import Mathlib
import Definitions.Def_DynRiskEq_Welfare_Model

open StochasticProg.Multistage FirstOrderOpt.ConvexTheory
open scoped RealInnerProductSpace

namespace DynRiskEq.Welfare

/-- Theorem 3(i) (p. 15). In a multistage risk-trading equilibrium the security prices restricted
to the children of every non-leaf node lie in every agent's risk set, hence in the social planning
risk set. -/
theorem theorem_3_i {H : ℕ} (T : Tree H) {A : Type} [Fintype A] [DecidableEq A]
    (M : Market T A) (Ka : A → T.Node → ℕ)
    (pa : (a : A) → (n : T.Node) → Fin (Ka a n) → T.Node → ℝ)
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ)
    (hRTE : IsRTE T M Ka pa π α μ u x W θa) :
    ∀ n, ¬ IsLeaf T n →
      (∀ a, InRisk T (Ka a) (pa a) n μ) ∧ restrictChildren T μ n ∈ socialRiskSet T Ka pa n := by sorry

end DynRiskEq.Welfare
