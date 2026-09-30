-- Prove2me | Theorems.Thm_BayesRouting_VOI_feasible_flows_eq
-- name    : BayesRouting.VOI.feasible_flows_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T15:00:38.141375+00:00
-- url     : https://prove2.me/theorems/dcfab57e-035c-4bed-8392-9e5ad13d188d
-- title:
--   Proposition 1 (first claim) — the feasible route flows are the convex polytope $\mathcal F(\lambda)$
-- statement:
--   Let $\lambda$ be in the simplex. A route flow $f$ is induced by some feasible strategy profile $q\in\mathcal Q(\lambda)$, i.e. $f_r(t)=\sum_i q^i_r(t^i)$, if and only if $f$ satisfies (14a)–(14d):
--
--   $$\{(\textstyle\sum_iq^i_r(t^i))_{r,t}:\ q\in\mathcal Q(\lambda)\}=\mathcal F(\lambda).$$
--
--   Moreover $\mathcal F(\lambda)$ is a convex polytope: it is the convex hull of finitely many route flows.
--
--   This lets the equilibrium analysis be carried out over route flows, where the size vector enters only through the constraints (IIC).
--
--   **Formalization Note** "Convex polytope" is stated as the convex hull of a finite set of route flows. The second part of Proposition 1 (the parametrization (19)–(20) of the strategy profiles inducing a given flow) is not stated.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 155, Proposition 1, first sentence

import Mathlib
import Definitions.Def_BayesRouting_VOI_Game
import Definitions.Def_BayesRouting_VOI_Potential
import Definitions.Def_BayesRouting_VOI_Flows

namespace BayesRouting.VOI

/-- **Proposition 1, first claim** (Wu, Amin, Ozdaglar, Oper. Res. 69(1) 2021, p. 155). For `λ` in
the simplex, the route flows induced by feasible strategy profiles are exactly the flows
satisfying (14a)–(14d), and this set `ℱ(λ)` is a convex polytope: the convex hull of finitely
many route flows. -/
theorem feasible_flows_eq {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (lam : I → ℝ) (hlam : lam ∈ stdSimplex ℝ I) :
    routeFlow '' feasibleStrategies G lam = feasibleFlows G lam ∧
      ∃ P : Set (R → ((i : I) → T i) → ℝ), P.Finite ∧
        feasibleFlows G lam = convexHull ℝ P := by sorry

end BayesRouting.VOI
