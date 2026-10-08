-- Prove2me | Theorems.Thm_DataDrivenRO_Discrete_theorem_4
-- name    : DataDrivenRO.Discrete.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:43:55.522255+00:00
-- url     : https://prove2.me/theorems/d97316e3-8907-4713-84cd-d06ea498c582
-- title:
--   Theorem 4 — χ² and G uncertainty sets bound worst-case VaR
-- statement:
--   Fix listed support vectors $a_j\in\mathbb R^d$, an empirical probability vector $\hat p\in\Delta_n$, and a nonnegative test radius $\rho$. The Pearson and G confidence regions of (10) determine the uncertainty sets of (12) and (13). Simultaneously for every tail level $0<\epsilon<1$, every law $P_p$ with $p$ in either region, and every direction $v$,
--
--   $$
--   \operatorname{VaR}^{P_p}_{\epsilon}(v)
--     \le\delta^*(v\mid U^{\chi^2}_\epsilon)
--     \quad(p\in\mathcal P^{\chi^2}),\qquad
--   \operatorname{VaR}^{P_p}_{\epsilon}(v)
--     \le\delta^*(v\mid U^G_\epsilon)
--     \quad(p\in\mathcal P^G).
--   $$
--
--   Both uncertainty sets are nonempty, convex, and compact. Thus their support functions are genuine finite suprema, and Theorem 1's geometric criterion turns these bounds into probabilistic guarantees whenever the confidence regions cover the true law.
--
--   **Formalization Note** This statement formalizes Theorem 4's deterministic risk-bound content. The paper's sampling probability comes from coverage of the Pearson and G tests, which is not asserted here. The test threshold is represented by an arbitrary $\rho\ge0$, corresponding to $\chi^2_{n-1,1-\alpha}/(2N)$. The explicit conic support-function programs (14)–(15) are separate, unformalized companions. The set of listed support points is represented by `Fin n`, and $P_p$ is the corresponding point-mass law.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 4 and (12)–(13), p. 13; proof, p. ec2

import Mathlib
import Definitions.Def_DataDrivenRO_Discrete_Setting

namespace DataDrivenRO.Discrete

/-- Deterministic content of Theorem 4, p. 13: for every tail level, both uncertainty sets
bound the Value at Risk of each law in the corresponding confidence region.  Their geometric
properties make the real support functions genuine and allow Theorem 1(a) to apply. -/
theorem theorem_4 {d n : ℕ} (a : Fin n → (Fin d → ℝ))
    (phat : Fin n → ℝ) (hphat : phat ∈ stdSimplex ℝ (Fin n))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∀ p ∈ chi2Region phat ρ, ∀ v : Fin d → ℝ,
        VaR a p ε v ≤ RobustMDP.Shared.supportFunction (Uchi2 a phat ρ ε) v) ∧
      (∀ p ∈ gRegion phat ρ, ∀ v : Fin d → ℝ,
        VaR a p ε v ≤ RobustMDP.Shared.supportFunction (UG a phat ρ ε) v) ∧
      (Uchi2 a phat ρ ε).Nonempty ∧ Convex ℝ (Uchi2 a phat ρ ε) ∧
        IsCompact (Uchi2 a phat ρ ε) ∧
      (UG a phat ρ ε).Nonempty ∧ Convex ℝ (UG a phat ρ ε) ∧
        IsCompact (UG a phat ρ ε) := by sorry

end DataDrivenRO.Discrete
