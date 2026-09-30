-- Prove2me | Theorems.Thm_BayesRouting_Adoption_adoption_rates_eq
-- name    : BayesRouting.Adoption.adoption_rates_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T15:26:26.673971+00:00
-- url     : https://prove2.me/theorems/95b82d66-79be-43dd-9303-4181818dba03
-- title:
--   Theorem 4 — the set of equilibrium adoption rates of the TIS is Λ†
-- statement:
--   Let $\Gamma(\lambda)$ be the Bayesian routing game with a nonempty finite set $\mathcal I$ of traffic information systems (standing assumptions as in the game definition), and consider the two-stage game in which travelers first subscribe to one TIS, inducing the size vector $\lambda$, and then play $\Gamma(\lambda)$. Let $\Lambda^\dagger$ be the set (30).
--
--   For every size vector $\lambda$ with $\lambda^i\ge0$, $\sum_i\lambda^i=1$, and every Bayesian Wardrop equilibrium $q$ of $\Gamma(\lambda)$ with equilibrium population costs $C^{i*}(\lambda)$,
--   $$\Big(\lambda^i>0\ \Rightarrow\ C^{i*}(\lambda)=\min_{j\in\mathcal I}C^{j*}(\lambda)\quad\forall i\in\mathcal I\Big)\iff\lambda\in\Lambda^\dagger.$$
--   Together with the existence of a BWE for every $\lambda$ in the simplex, this says that the set of equilibrium adoption rates under the choice of TIS is exactly $\Lambda^\dagger$.
--
--   The result characterizes which market shares of competing information systems are stable when travelers choose their TIS: exactly the size vectors minimizing the equilibrium potential. In general $\Lambda^\dagger$ is not a single point, so the equilibrium adoption rate of each TIS ranges over an interval.
--
--   **Formalization Note** The statement is made for every BWE $q$ of $\Gamma(\lambda)$ (the population costs do not depend on the equilibrium chosen), which also asserts that no BWE of a $\lambda\notin\Lambda^\dagger$ satisfies the adoption condition. The population costs are the last form of the paper's (7), which is also the cost of an individual subscriber to an unused TIS ($\lambda^i=0$).
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 161, Theorem 4 (with (30)-(31))

import Mathlib
import Definitions.Def_BayesRouting_Adoption_Game
import Definitions.Def_BayesRouting_Adoption_Potential
import Definitions.Def_BayesRouting_Adoption_Flows
import Definitions.Def_BayesRouting_Adoption_SizeSets

open Finset

namespace BayesRouting.Adoption

/-- Theorem 4 (p. 161). For every size vector `λ` in the simplex and every BWE `q` of `Γ(λ)`,
`λ` is a vector of equilibrium adoption rates (condition (31) holds at `q`) if and only if
`λ ∈ Λ†`. -/
theorem adoption_rates_eq {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {T : I → Type}
    [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type}
    [Fintype S] [Fintype E] [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) :
    ∀ lam ∈ stdSimplex ℝ I, ∀ q, IsBWE G lam q →
      (IsAdoptionEq G lam q ↔ lam ∈ sizeIndepSet G) := by sorry

end BayesRouting.Adoption
