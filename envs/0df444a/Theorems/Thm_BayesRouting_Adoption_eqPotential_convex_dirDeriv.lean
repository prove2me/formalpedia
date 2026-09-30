-- Prove2me | Theorems.Thm_BayesRouting_Adoption_eqPotential_convex_dirDeriv
-- name    : BayesRouting.Adoption.eqPotential_convex_dirDeriv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T15:23:25.299739+00:00
-- url     : https://prove2.me/theorems/a7db1140-8a25-433d-86e1-5f65cd584c78
-- title:
--   Lemma 5 — Ψ(λ) is convex, and its derivative in direction z^{ij} is −D·V^{ij*}(λ)
-- statement:
--   Let $\Gamma(\lambda)$ be the Bayesian routing game (standing assumptions as in the game definition) and let $\Psi(\lambda)$ be the minimum of the weighted potential over $\mathcal Q(\lambda)$.
--
--   1. $\Psi$ is convex on the simplex $\{\lambda:\lambda^i\ge0,\ \sum_i\lambda^i=1\}$.
--   2. Let $i,j\in\mathcal I$, let $\lambda$ be in the simplex with $\lambda^j>0$, and let $q$ be any BWE of $\Gamma(\lambda)$ with population costs $C^{i*}(\lambda)$, $C^{j*}(\lambda)$. Write $V^{ij*}(\lambda)=C^{j*}(\lambda)-C^{i*}(\lambda)$. Then the one-sided directional derivative of $\Psi$ at $\lambda$ in the direction $z^{ij}$ exists and
--   $$\nabla_{z^{ij}}\Psi(\lambda):=\lim_{\epsilon\to0^+}\frac{\Psi(\lambda+\epsilon z^{ij})-\Psi(\lambda)}{\epsilon}=-D\,V^{ij*}(\lambda),$$
--   which is the paper's identity $V^{ij*}(\lambda)=-\frac1D\nabla_{z^{ij}}\Psi(\lambda)$ (26).
--
--   The lemma links the potential's geometry to the travelers' costs: moving mass from population $j$ to population $i$ changes $\Psi$ at rate proportional to the cost difference between the two populations. The case $\lambda^i=0$ is included; it is where (26) describes an unused TIS.
--
--   **Formalization Note** The hypothesis $\lambda^j>0$ is added: if $\lambda^j=0$, the point $\lambda+\epsilon z^{ij}$ leaves the simplex for every $\epsilon>0$ and $\Psi$ is not defined there (the paper considers only feasible size vectors). The paper's "directionally differentiable in $\lambda$" is stated for the directions $z^{ij}$, the ones (26) concerns. The statement holds for every BWE $q$, since the population costs do not depend on the equilibrium chosen.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 158, Lemma 5 eq. (26); V^{ij*} defined on p. 157

import Mathlib
import Definitions.Def_BayesRouting_Adoption_Game
import Definitions.Def_BayesRouting_Adoption_Potential
import Definitions.Def_BayesRouting_Adoption_Flows
import Definitions.Def_BayesRouting_Adoption_SizeSets

open Finset Filter Topology

namespace BayesRouting.Adoption

/-- Lemma 5 (p. 158). The equilibrium potential `Ψ` is convex on the simplex of size vectors, and
for populations `i, j`, a size vector `λ` in the simplex with `λ^j > 0` and any BWE `q` of `Γ(λ)`,
the one-sided derivative of `Ψ` at `λ` in the direction `z^{ij}` exists and equals
`-D · V^{ij*}(λ) = -D (C^{j*}(λ) - C^{i*}(λ))`, which is (26). `λ^i = 0` is allowed. -/
theorem eqPotential_convex_dirDeriv {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) :
    ConvexOn ℝ (stdSimplex ℝ I) (eqPotential G) ∧
    ∀ (i j : I) (lam : I → ℝ), lam ∈ stdSimplex ℝ I → 0 < lam j →
      ∀ q, IsBWE G lam q →
        Tendsto (fun ε : ℝ => (eqPotential G (lam + ε • pairDir i j) - eqPotential G lam) / ε)
          (𝓝[>] 0) (𝓝 (-(G.D) * (popCost G q j - popCost G q i))) := by sorry

end BayesRouting.Adoption
