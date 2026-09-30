-- Prove2me | Theorems.Thm_BayesRouting_Adoption_sizeIndepSet_eq_argmin
-- name    : BayesRouting.Adoption.sizeIndepSet_eq_argmin
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T15:24:53.800381+00:00
-- url     : https://prove2.me/theorems/e269d45d-cada-46b5-8c8e-1155daf3cd5e
-- title:
--   Proposition 5 — Λ† is convex and equals argmin Ψ; the equilibrium edge load equals w† iff λ ∈ Λ†
-- statement:
--   Let $\Gamma(\lambda)$ be the Bayesian routing game (standing assumptions as in the game definition), $\mathcal F^\dagger$ the optimal solution set of problem (28) and $\Lambda^\dagger$ the set (30). Let $\Delta=\{\lambda:\lambda^i\ge0,\ \sum_i\lambda^i=1\}$.
--
--   1. $\Lambda^\dagger$ is convex.
--   2. $\Lambda^\dagger$ is the set of minimizers of $\Psi$ over the feasible size vectors:
--   $$\Lambda^\dagger=\operatorname*{argmin}_{\lambda\in\Delta}\Psi(\lambda).$$
--   3. For $\lambda\in\Delta$ and any BWE $q$ of $\Gamma(\lambda)$ with edge load $w^*(\lambda)$: if $\lambda\in\Lambda^\dagger$, then $w^*(\lambda)$ equals the edge load $w^\dagger$ of every $f^\dagger\in\mathcal F^\dagger$; conversely, if $w^*(\lambda)$ equals the edge load of some $f^\dagger\in\mathcal F^\dagger$, then $\lambda\in\Lambda^\dagger$.
--
--   Part 3 is the size-independence of the equilibrium edge load: on $\Lambda^\dagger$ the load is the fixed vector $w^\dagger$, which does not depend on $\lambda$, and outside $\Lambda^\dagger$ it differs from $w^\dagger$. Part 2 is what turns the adoption question into the minimization of $\Psi$.
--
--   **Formalization Note** The edge load $w^\dagger$ is not a separate object: part 3 compares $w^*(\lambda)$ with the edge loads of the elements of $\mathcal F^\dagger$ (which all coincide under the standing assumption that every type profile has positive probability).
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 161, Proposition 5 (with (28)-(30), pp. 160-161)

import Mathlib
import Definitions.Def_BayesRouting_Adoption_Game
import Definitions.Def_BayesRouting_Adoption_Potential
import Definitions.Def_BayesRouting_Adoption_Flows
import Definitions.Def_BayesRouting_Adoption_SizeSets

open Finset

namespace BayesRouting.Adoption

/-- Proposition 5 (p. 161). The set `Λ†` of (30) is convex and is the set of minimizers of the
equilibrium potential `Ψ` over the simplex of size vectors. Moreover, for `λ` in the simplex and
any BWE `q` of `Γ(λ)`: if `λ ∈ Λ†`, the equilibrium edge load of `q` equals the edge load of every
`f† ∈ ℱ†` (the size-independent load `w†`); and if the equilibrium edge load equals the edge load
of some `f† ∈ ℱ†`, then `λ ∈ Λ†`. -/
theorem sizeIndepSet_eq_argmin {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) :
    Convex ℝ (sizeIndepSet G) ∧
    sizeIndepSet G =
      {lam | lam ∈ stdSimplex ℝ I ∧
        ∀ lam' ∈ stdSimplex ℝ I, eqPotential G lam ≤ eqPotential G lam'} ∧
    ∀ lam ∈ stdSimplex ℝ I, ∀ q, IsBWE G lam q →
      (lam ∈ sizeIndepSet G →
          ∀ f ∈ optFlowsUnconstrained G, edgeLoad G q = flowLoad G f) ∧
      ((∃ f ∈ optFlowsUnconstrained G, edgeLoad G q = flowLoad G f) →
          lam ∈ sizeIndepSet G) := by sorry

end BayesRouting.Adoption
