-- Prove2me | Theorems.Thm_DuffieHedge_Optimal_exists_Gstar
-- name    : DuffieHedge.Optimal.exists_Gstar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:16:51.915583+00:00
-- url     : https://prove2.me/theorems/954059d1-1884-4061-9f7e-0c3f6fcadffb
-- title:
--   §3.3, p. 5 — existence of a solution $G^*$ of (10), with $G^*_t\in L^2(P)$
-- statement:
--   Under the standing hypotheses, for every commitment $k$ and target $L$ the stochastic differential equation (10),
--
--   $$dG^*_t=\Phi(G^*_t)\,dF_t,\qquad G^*_0=0,$$
--
--   with the feedback map $\Phi$ of (11), has a solution $G^*$ on $[0,T]$, and $G^*_t\in L^2(P)$ for every $t\in[0,T]$.
--
--   The paper cites this as standard (Protter 1990). It is what makes the strategy $\Phi(G^*)$ of Proposition 1 refer to anything.
--
--   **Formalization Note.** A solution means that $\varphi_t=\Phi_t(G^*_t)$ is a trading strategy and $G^*$ is a version of its futures gain; the paper takes $\varphi\in\Theta$ for granted, and here it is part of the conclusion.
-- source:
--   Duffie and Richardson, Mean-Variance Hedging in Continuous Time, Ann. Appl. Probab. 1(1) (1991), §3.3, after (11), p. 5

import Mathlib
import Definitions.Def_DuffieHedge_Optimal_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DuffieHedge.Optimal

/-- §3.3, after (11) (p. 5): the SDE (10), `dG*_t = Φ(G*_t) dF_t`, `G*₀ = 0`, has a solution
`G*` (with `Φ(G*)` a trading strategy), and `G*_t ∈ L²(P)` for every `t ∈ [0, T]`. -/
theorem exists_Gstar {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Standing)
    (k L : ℝ) :
    ∃ Gs : ℝ≥0 → Ω → ℝ, M.SolvesEq10 k L Gs ∧ ∀ t ≤ M.T, MemLp (Gs t) 2 M.P := by sorry

end DuffieHedge.Optimal
