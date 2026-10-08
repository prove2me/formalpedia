-- Prove2me | Theorems.Thm_DataDrivenRO_Discrete_support_eq_sup_cvar
-- name    : DataDrivenRO.Discrete.support_eq_sup_cvar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:43:57.562989+00:00
-- url     : https://prove2.me/theorems/f792e371-2477-4719-970f-ff6c6cdd277e
-- title:
--   Proof of Theorem 4 — the support functions are worst-case CVaR
-- statement:
--   Fix a probability vector $\hat p\in\Delta_n$, a nonnegative radius $\rho$, and $0<\epsilon<1$. For each direction $v$, the support function of $U^{\chi^2}_\epsilon$ is the least upper bound of $\operatorname{CVaR}^{P_p}_\epsilon(v)$ over $p\in\mathcal P^{\chi^2}$. The same assertion holds for $U^G_\epsilon$ and $\mathcal P^G$:
--
--   $$
--   \delta^*(v\mid U^{\chi^2}_\epsilon)
--     =\sup_{p\in\mathcal P^{\chi^2}}\operatorname{CVaR}^{P_p}_\epsilon(v),\qquad
--   \delta^*(v\mid U^G_\epsilon)
--     =\sup_{p\in\mathcal P^G}\operatorname{CVaR}^{P_p}_\epsilon(v).
--   $$
--
--   In each case, a point of the uncertainty set attains the displayed support value, as in the paper's final maximum. These identities express the two data-driven sets as unions of the CVaR reweighting sets and connect Theorem EC.1 to Theorem 4.
--
--   **Formalization Note** `IsLUB` states each supremum without assigning a default value to an empty or unbounded family. The nonnegative radius and simplex center ensure the families are nonempty; both uncertainty sets are bounded.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, proof of Theorem 4, final equality of displayed chain, p. ec2

import Mathlib
import Definitions.Def_DataDrivenRO_Discrete_Setting

namespace DataDrivenRO.Discrete

/-- The last equality in the proof of Theorem 4, p. ec2, for both confidence regions. -/
theorem support_eq_sup_cvar {d n : ℕ} (a : Fin n → (Fin d → ℝ))
    (phat : Fin n → ℝ) (hphat : phat ∈ stdSimplex ℝ (Fin n))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (v : Fin d → ℝ) :
    IsLUB ((fun p => CVaR a p ε v) '' chi2Region phat ρ)
      (RobustMDP.Shared.supportFunction (Uchi2 a phat ρ ε) v) ∧
    (∃ u ∈ Uchi2 a phat ρ ε,
      u ⬝ᵥ v = RobustMDP.Shared.supportFunction (Uchi2 a phat ρ ε) v) ∧
    IsLUB ((fun p => CVaR a p ε v) '' gRegion phat ρ)
      (RobustMDP.Shared.supportFunction (UG a phat ρ ε) v) ∧
    (∃ u ∈ UG a phat ρ ε,
      u ⬝ᵥ v = RobustMDP.Shared.supportFunction (UG a phat ρ ε) v) := by sorry

end DataDrivenRO.Discrete
