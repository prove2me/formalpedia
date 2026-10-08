-- Prove2me | Theorems.Thm_DataDrivenRO_Discrete_var_le_cvar
-- name    : DataDrivenRO.Discrete.var_le_cvar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:43:39.49867+00:00
-- url     : https://prove2.me/theorems/16190d2f-bbec-4ef8-92a0-3e2c55c139ee
-- title:
--   CVaR upper-bounds VaR for a finite-support law
-- statement:
--   Let $p\in\Delta_n$ assign masses to the listed support vectors $a_j\in\mathbb R^d$. For every $0<\epsilon<1$ and direction $v\in\mathbb R^d$, conditional value at risk at tail level $\epsilon$ bounds value at risk at the same level:
--
--   $$
--   \operatorname{VaR}^{P_p}_{\epsilon}(v)\le
--   \operatorname{CVaR}^{P_p}_{\epsilon}(v).
--   $$
--
--   The same conditional-value-at-risk function is convex as a function of the direction $v$. The inequality is used in the first line of the proof of Theorem 4.
--
--   **Formalization Note** $P_p$ is the finitely supported point-mass law. The simplex hypothesis makes it a probability law and prevents the real infima from taking default values.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, sentence following (11), p. 12; proof of Theorem 4, p. ec2

import Mathlib
import Definitions.Def_DataDrivenRO_Discrete_Setting

namespace DataDrivenRO.Discrete

/-- Conditional Value at Risk is an upper bound on Value at Risk for the same finite-support
law and tail level.  Sentence following (11), p. 12. -/
theorem var_le_cvar {d n : ℕ} (a : Fin n → (Fin d → ℝ)) (p : Fin n → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (v : Fin d → ℝ) :
    VaR a p ε v ≤ CVaR a p ε v ∧
      ConvexOn ℝ Set.univ (fun w : Fin d → ℝ => CVaR a p ε w) := by sorry

end DataDrivenRO.Discrete
