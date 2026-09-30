-- Prove2me | Theorems.Thm_BayesRouting_VOI_eqFlows_eq_argmin
-- name    : BayesRouting.VOI.eqFlows_eq_argmin
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T15:03:17.17242+00:00
-- url     : https://prove2.me/theorems/3473ef8a-a61b-467a-9c36-5063572f4542
-- title:
--   Proposition 2 — equilibrium route flows are the minimizers of $\widehat\Phi$ over $\mathcal F(\lambda)$
-- statement:
--   Let $\lambda$ be in the simplex and $f\in\mathcal F(\lambda)$ a feasible route flow. Then $f$ is an equilibrium route flow, $f\in\mathcal F^*(\lambda)$ (induced by some BWE of $\Gamma(\lambda)$), if and only if $f$ is an optimal solution of
--
--   $$\min\ \widehat\Phi(f)\quad\text{s.t.}\quad f\in\mathcal F(\lambda).\qquad(\text{OPT-}\mathcal F)$$
--
--   This is the route-flow analogue of Theorem 1 and the starting point of the regime analysis.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 156, Proposition 2

import Mathlib
import Definitions.Def_BayesRouting_VOI_Game
import Definitions.Def_BayesRouting_VOI_Potential
import Definitions.Def_BayesRouting_VOI_Flows

namespace BayesRouting.VOI

/-- **Proposition 2** (Wu, Amin, Ozdaglar, Oper. Res. 69(1) 2021, p. 156). For `λ` in the
simplex, a feasible route flow `f ∈ ℱ(λ)` is an equilibrium route flow if and only if it minimizes
`Φ̂` over `ℱ(λ)` (OPT-ℱ). -/
theorem eqFlows_eq_argmin {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (lam : I → ℝ) (hlam : lam ∈ stdSimplex ℝ I)
    (f : R → ((i : I) → T i) → ℝ) (hf : f ∈ feasibleFlows G lam) :
    f ∈ eqFlows G lam ↔
      ∀ g ∈ feasibleFlows G lam, flowPotential G f ≤ flowPotential G g := by sorry

end BayesRouting.VOI
