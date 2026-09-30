-- Prove2me | Theorems.Thm_BayesRouting_Adoption_eqFlows_eq_argmin
-- name    : BayesRouting.Adoption.eqFlows_eq_argmin
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T15:22:06.837933+00:00
-- url     : https://prove2.me/theorems/8b05577a-5089-4108-a61a-6e1ecb718f85
-- title:
--   Proposition 2 — equilibrium route flows are the minimizers of Φ̂ over the flow polytope ℱ(λ)
-- statement:
--   Let $\Gamma(\lambda)$ be the Bayesian routing game (standing assumptions as in the game definition) and let $\lambda$ satisfy $\lambda^i\ge0$, $\sum_i\lambda^i=1$. A feasible route flow $f\in\mathcal F(\lambda)$ (constraints (14a)–(14d)) is an equilibrium route flow, i.e. $f$ is induced by some BWE of $\Gamma(\lambda)$, if and only if $f$ is an optimal solution of
--   $$\min\ \widehat\Phi(f)\quad\text{s.t.}\quad f\in\mathcal F(\lambda).\tag{OPT-$\mathcal F$}$$
--
--   This moves the equilibrium problem from strategy profiles to route flows, where the population sizes enter only through the information impact constraints $\widehat J^i(f)\le\lambda^iD$. Dropping all of these constraints gives problem (28), whose optimal solutions form $\mathcal F^\dagger$.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 156, Proposition 2

import Mathlib
import Definitions.Def_BayesRouting_Adoption_Game
import Definitions.Def_BayesRouting_Adoption_Potential
import Definitions.Def_BayesRouting_Adoption_Flows

open Finset

namespace BayesRouting.Adoption

/-- Proposition 2 (p. 156). For `λ` in the simplex, a feasible route flow `f ∈ ℱ(λ)` is an
equilibrium route flow (induced by a BWE of `Γ(λ)`) if and only if it minimizes `Φ̂` over `ℱ(λ)`
(problem (OPT-ℱ)). -/
theorem eqFlows_eq_argmin {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (lam : I → ℝ) (hlam : lam ∈ stdSimplex ℝ I)
    (f : R → ((i : I) → T i) → ℝ) (hf : f ∈ feasibleFlows G lam) :
    f ∈ eqFlows G lam ↔
      ∀ g ∈ feasibleFlows G lam, flowPotential G f ≤ flowPotential G g := by sorry

end BayesRouting.Adoption
